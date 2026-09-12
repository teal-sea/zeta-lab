import FourPoint.Cells

/-! Chunk module 8 of 16 of the three-dimensional table.  Each lemma is one
subtree of at most 110 leaves of one box's bisection tree; `FourPoint/Boxes.lean` routes
the box down to them.  Cutting the tree this way gives each subtree its own
heartbeat budget and lets `lake` compile them in parallel. -/

noncomputable section
namespace Zeta23Ext.Bridge.FourPoint

set_option maxHeartbeats 20000000 in
lemma ch_23 (x y z : ℝ) (hx1 : (267/256:ℝ) ≤ x) (hx2 : x ≤ (1073/1024:ℝ))
    (hy1 : (2021/1024:ℝ) ≤ y) (hy2 : y ≤ (1013/512:ℝ))
    (hz1 : (267/256:ℝ) ≤ z) (hz2 : z ≤ (1073/1024:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (2141/2048:ℝ) with hc | hc
  · rcases le_total y (4047/2048:ℝ) with hc | hc
    · rcases le_total z (2141/2048:ℝ) with hc | hc
      · rcases le_total x (4277/4096:ℝ) with hc | hc
        · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
          have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_95 y (by linarith) (by linarith)
          have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
          have hw5 : (81942717/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_559 (x + y + z) (by linarith) (by linarith)
          linarith
        · rcases le_total y (8089/4096:ℝ) with hc | hc
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
            have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_94 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
            have hw5 : (865374359/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_567 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
            have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_97 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
            have hw5 : (227869559/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_569 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total x (4277/4096:ℝ) with hc | hc
        · rcases le_total y (8089/4096:ℝ) with hc | hc
          · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
            have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_94 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_236 (x + y) (by linarith) (by linarith)
            have hw5 : (227869559/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_569 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
            have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_97 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw4 : (41/1250000000000:ℝ) ≤ wfun (y + z) := wc_238 (y + z) (by linarith) (by linarith)
            have hw5 : (958721819/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_576 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (8089/4096:ℝ) with hc | hc
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
            have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_94 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw5 : (958721819/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_576 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total z (4287/4096:ℝ) with hc | hc
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
              have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_97 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
              have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_237 (y + z) (by linarith) (by linarith)
              have hw5 : (126039153/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_578 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
              have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_97 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
              have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_240 (y + z) (by linarith) (by linarith)
              have hw5 : (1057880619/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_590 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total z (2141/2048:ℝ) with hc | hc
      · rcases le_total x (4277/4096:ℝ) with hc | hc
        · rcases le_total y (8099/4096:ℝ) with hc | hc
          · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
            have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
            have hw5 : (227869559/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_569 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total z (4277/4096:ℝ) with hc | hc
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
              have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_237 (x + y) (by linarith) (by linarith)
              have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_237 (y + z) (by linarith) (by linarith)
              have hw5 : (959876941/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_575 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
              have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_237 (x + y) (by linarith) (by linarith)
              have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_240 (y + z) (by linarith) (by linarith)
              have hw5 : (126039153/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_578 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (8099/4096:ℝ) with hc | hc
          · rcases le_total z (4277/4096:ℝ) with hc | hc
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
              have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_237 (x + y) (by linarith) (by linarith)
              have hw5 : (959876941/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_575 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
              have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_237 (x + y) (by linarith) (by linarith)
              have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_237 (y + z) (by linarith) (by linarith)
              have hw5 : (126039153/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_578 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (4277/4096:ℝ) with hc | hc
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
              have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
              have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_240 (x + y) (by linarith) (by linarith)
              have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_237 (y + z) (by linarith) (by linarith)
              have hw5 : (126039153/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_578 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
              have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
              have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_240 (x + y) (by linarith) (by linarith)
              have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_240 (y + z) (by linarith) (by linarith)
              have hw5 : (1057880619/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_590 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (4277/4096:ℝ) with hc | hc
        · rcases le_total y (8099/4096:ℝ) with hc | hc
          · rcases le_total z (4287/4096:ℝ) with hc | hc
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
              have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
              have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_240 (y + z) (by linarith) (by linarith)
              have hw5 : (126039153/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_578 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
              have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
              have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_250 (y + z) (by linarith) (by linarith)
              have hw5 : (1057880619/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_590 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (4287/4096:ℝ) with hc | hc
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
              have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_237 (x + y) (by linarith) (by linarith)
              have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_250 (y + z) (by linarith) (by linarith)
              have hw5 : (1057880619/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_590 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
              have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_237 (x + y) (by linarith) (by linarith)
              have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
              have hw5 : (1108574073/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_594 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (8099/4096:ℝ) with hc | hc
          · rcases le_total z (4287/4096:ℝ) with hc | hc
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
              have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_237 (x + y) (by linarith) (by linarith)
              have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_240 (y + z) (by linarith) (by linarith)
              have hw5 : (1057880619/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_590 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
              have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_237 (x + y) (by linarith) (by linarith)
              have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_250 (y + z) (by linarith) (by linarith)
              have hw5 : (1108574073/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_594 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (4287/4096:ℝ) with hc | hc
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
              have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
              have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_240 (x + y) (by linarith) (by linarith)
              have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_250 (y + z) (by linarith) (by linarith)
              have hw5 : (1108574073/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_594 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (8559/8192:ℝ) with hc | hc
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_32 x (by linarith) (by linarith)
                have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (593183/5000000000000:ℝ) ≤ wfun (x + y) := wc_239 (x + y) (by linarith) (by linarith)
                have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
                have hw5 : (36283957/312500000000:ℝ) ≤ wfun (x + y + z) := wc_601 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (2638657/10000000000000:ℝ) ≤ wfun (x + y) := wc_248 (x + y) (by linarith) (by linarith)
                have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
                have hw5 : (118742829/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_605 (x + y + z) (by linarith) (by linarith)
                linarith
  · rcases le_total y (4047/2048:ℝ) with hc | hc
    · rcases le_total z (2141/2048:ℝ) with hc | hc
      · rcases le_total x (4287/4096:ℝ) with hc | hc
        · rcases le_total y (8089/4096:ℝ) with hc | hc
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
            have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_94 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
            have hw5 : (227869559/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_569 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
            have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_97 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
            have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_237 (x + y) (by linarith) (by linarith)
            have hw5 : (958721819/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_576 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (8089/4096:ℝ) with hc | hc
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
            have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_94 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
            have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_237 (x + y) (by linarith) (by linarith)
            have hw5 : (958721819/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_576 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total z (4277/4096:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_97 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
              have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_240 (x + y) (by linarith) (by linarith)
              have hw5 : (126039153/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_578 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_97 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
              have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_240 (x + y) (by linarith) (by linarith)
              have hw5 : (1057880619/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_590 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (4287/4096:ℝ) with hc | hc
        · rcases le_total y (8089/4096:ℝ) with hc | hc
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
            have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_94 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw5 : (1007100179/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_579 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total z (4287/4096:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
              have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_97 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_237 (x + y) (by linarith) (by linarith)
              have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_237 (y + z) (by linarith) (by linarith)
              have hw5 : (1057880619/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_590 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
              have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_97 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_237 (x + y) (by linarith) (by linarith)
              have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_240 (y + z) (by linarith) (by linarith)
              have hw5 : (1108574073/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_594 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (8089/4096:ℝ) with hc | hc
          · rcases le_total z (4287/4096:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_94 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_237 (x + y) (by linarith) (by linarith)
              have hw5 : (1057880619/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_590 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_94 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_237 (x + y) (by linarith) (by linarith)
              have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_237 (y + z) (by linarith) (by linarith)
              have hw5 : (1108574073/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_594 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (4287/4096:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_97 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
              have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_240 (x + y) (by linarith) (by linarith)
              have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_237 (y + z) (by linarith) (by linarith)
              have hw5 : (1108574073/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_594 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_97 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
              have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_240 (x + y) (by linarith) (by linarith)
              have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_240 (y + z) (by linarith) (by linarith)
              have hw5 : (290097117/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_602 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total z (2141/2048:ℝ) with hc | hc
      · rcases le_total x (4287/4096:ℝ) with hc | hc
        · rcases le_total y (8099/4096:ℝ) with hc | hc
          · rcases le_total z (4277/4096:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
              have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
              have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_240 (x + y) (by linarith) (by linarith)
              have hw5 : (126039153/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_578 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
              have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
              have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_240 (x + y) (by linarith) (by linarith)
              have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_237 (y + z) (by linarith) (by linarith)
              have hw5 : (1057880619/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_590 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (4277/4096:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
              have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
              have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_250 (x + y) (by linarith) (by linarith)
              have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_237 (y + z) (by linarith) (by linarith)
              have hw5 : (1057880619/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_590 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
              have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
              have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_250 (x + y) (by linarith) (by linarith)
              have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_240 (y + z) (by linarith) (by linarith)
              have hw5 : (1108574073/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_594 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (8099/4096:ℝ) with hc | hc
          · rcases le_total z (4277/4096:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
              have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_250 (x + y) (by linarith) (by linarith)
              have hw5 : (1057880619/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_590 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
              have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_250 (x + y) (by linarith) (by linarith)
              have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_237 (y + z) (by linarith) (by linarith)
              have hw5 : (1108574073/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_594 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (4277/4096:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
              have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_254 (x + y) (by linarith) (by linarith)
              have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_237 (y + z) (by linarith) (by linarith)
              have hw5 : (1108574073/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_594 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (8579/8192:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (5211923/5000000000000:ℝ) ≤ wfun (x + y) := wc_253 (x + y) (by linarith) (by linarith)
                have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_240 (y + z) (by linarith) (by linarith)
                have hw5 : (36283957/312500000000:ℝ) ≤ wfun (x + y + z) := wc_601 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (3539799/2500000000000:ℝ) ≤ wfun (x + y) := wc_259 (x + y) (by linarith) (by linarith)
                have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_240 (y + z) (by linarith) (by linarith)
                have hw5 : (118742829/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_605 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total x (4287/4096:ℝ) with hc | hc
        · rcases le_total y (8099/4096:ℝ) with hc | hc
          · rcases le_total z (4287/4096:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
              have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
              have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_240 (x + y) (by linarith) (by linarith)
              have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_240 (y + z) (by linarith) (by linarith)
              have hw5 : (1108574073/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_594 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (8569/8192:ℝ) with hc | hc
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (593183/5000000000000:ℝ) ≤ wfun (x + y) := wc_239 (x + y) (by linarith) (by linarith)
                have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_250 (y + z) (by linarith) (by linarith)
                have hw5 : (36283957/312500000000:ℝ) ≤ wfun (x + y + z) := wc_601 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (2638657/10000000000000:ℝ) ≤ wfun (x + y) := wc_248 (x + y) (by linarith) (by linarith)
                have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_250 (y + z) (by linarith) (by linarith)
                have hw5 : (118742829/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_605 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (4287/4096:ℝ) with hc | hc
            · rcases le_total x (8569/8192:ℝ) with hc | hc
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (4662827/10000000000000:ℝ) ≤ wfun (x + y) := wc_249 (x + y) (by linarith) (by linarith)
                have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_250 (y + z) (by linarith) (by linarith)
                have hw5 : (36283957/312500000000:ℝ) ≤ wfun (x + y + z) := wc_601 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (7258139/10000000000000:ℝ) ≤ wfun (x + y) := wc_252 (x + y) (by linarith) (by linarith)
                have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_250 (y + z) (by linarith) (by linarith)
                have hw5 : (118742829/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_605 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (8569/8192:ℝ) with hc | hc
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (4662827/10000000000000:ℝ) ≤ wfun (x + y) := wc_249 (x + y) (by linarith) (by linarith)
                have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
                have hw5 : (303512103/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_606 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (7258139/10000000000000:ℝ) ≤ wfun (x + y) := wc_252 (x + y) (by linarith) (by linarith)
                have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
                have hw5 : (124094633/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_617 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total y (8099/4096:ℝ) with hc | hc
          · rcases le_total z (4287/4096:ℝ) with hc | hc
            · rcases le_total x (8579/8192:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (4662827/10000000000000:ℝ) ≤ wfun (x + y) := wc_249 (x + y) (by linarith) (by linarith)
                have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_240 (y + z) (by linarith) (by linarith)
                have hw5 : (36283957/312500000000:ℝ) ≤ wfun (x + y + z) := wc_601 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (7258139/10000000000000:ℝ) ≤ wfun (x + y) := wc_252 (x + y) (by linarith) (by linarith)
                have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_240 (y + z) (by linarith) (by linarith)
                have hw5 : (118742829/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_605 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (8579/8192:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (4662827/10000000000000:ℝ) ≤ wfun (x + y) := wc_249 (x + y) (by linarith) (by linarith)
                have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_250 (y + z) (by linarith) (by linarith)
                have hw5 : (303512103/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_606 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (7258139/10000000000000:ℝ) ≤ wfun (x + y) := wc_252 (x + y) (by linarith) (by linarith)
                have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_250 (y + z) (by linarith) (by linarith)
                have hw5 : (124094633/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_617 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (4287/4096:ℝ) with hc | hc
            · rcases le_total x (8579/8192:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (5211923/5000000000000:ℝ) ≤ wfun (x + y) := wc_253 (x + y) (by linarith) (by linarith)
                have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_250 (y + z) (by linarith) (by linarith)
                have hw5 : (303512103/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_606 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (3539799/2500000000000:ℝ) ≤ wfun (x + y) := wc_259 (x + y) (by linarith) (by linarith)
                have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_250 (y + z) (by linarith) (by linarith)
                have hw5 : (124094633/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_617 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (8579/8192:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (5211923/5000000000000:ℝ) ≤ wfun (x + y) := wc_253 (x + y) (by linarith) (by linarith)
                have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
                have hw5 : (634060693/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_619 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (3539799/2500000000000:ℝ) ≤ wfun (x + y) := wc_259 (x + y) (by linarith) (by linarith)
                have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
                have hw5 : (647786457/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_624 (x + y + z) (by linarith) (by linarith)
                linarith

set_option maxHeartbeats 20000000 in
lemma ch_30 (x y z : ℝ) (hx1 : (267/256:ℝ) ≤ x) (hx2 : x ≤ (1073/1024:ℝ))
    (hy1 : (1013/512:ℝ) ≤ y) (hy2 : y ≤ (2031/1024:ℝ))
    (hz1 : (1073/1024:ℝ) ≤ z) (hz2 : z ≤ (539/512:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (2141/2048:ℝ) with hc | hc
  · rcases le_total y (4057/2048:ℝ) with hc | hc
    · rcases le_total z (2151/2048:ℝ) with hc | hc
      · rcases le_total x (4277/4096:ℝ) with hc | hc
        · rcases le_total y (8109/4096:ℝ) with hc | hc
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
              have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
              have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_240 (x + y) (by linarith) (by linarith)
              have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_268 (y + z) (by linarith) (by linarith)
              have hw5 : (1213318631/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_607 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
              have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_240 (x + y) (by linarith) (by linarith)
              have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
              have hw5 : (1267359331/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_620 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · rcases le_total x (8549/8192:ℝ) with hc | hc
              · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_26 x (by linarith) (by linarith)
                have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (4662827/10000000000000:ℝ) ≤ wfun (x + y) := wc_249 (x + y) (by linarith) (by linarith)
                have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
                have hw5 : (634060693/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_619 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_31 x (by linarith) (by linarith)
                have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (7258139/10000000000000:ℝ) ≤ wfun (x + y) := wc_252 (x + y) (by linarith) (by linarith)
                have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
                have hw5 : (647786457/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_624 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
              have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_250 (x + y) (by linarith) (by linarith)
              have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
              have hw5 : (52900211/400000000000:ℝ) ≤ wfun (x + y + z) := wc_628 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (8109/4096:ℝ) with hc | hc
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · rcases le_total x (8559/8192:ℝ) with hc | hc
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_32 x (by linarith) (by linarith)
                have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (4662827/10000000000000:ℝ) ≤ wfun (x + y) := wc_249 (x + y) (by linarith) (by linarith)
                have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_268 (y + z) (by linarith) (by linarith)
                have hw5 : (634060693/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_619 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (7258139/10000000000000:ℝ) ≤ wfun (x + y) := wc_252 (x + y) (by linarith) (by linarith)
                have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_268 (y + z) (by linarith) (by linarith)
                have hw5 : (647786457/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_624 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (8559/8192:ℝ) with hc | hc
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_32 x (by linarith) (by linarith)
                have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (4662827/10000000000000:ℝ) ≤ wfun (x + y) := wc_249 (x + y) (by linarith) (by linarith)
                have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
                have hw5 : (1323300249/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_627 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (7258139/10000000000000:ℝ) ≤ wfun (x + y) := wc_252 (x + y) (by linarith) (by linarith)
                have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
                have hw5 : (1351302719/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_635 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · rcases le_total x (8559/8192:ℝ) with hc | hc
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_32 x (by linarith) (by linarith)
                have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (5211923/5000000000000:ℝ) ≤ wfun (x + y) := wc_253 (x + y) (by linarith) (by linarith)
                have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
                have hw5 : (1323300249/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_627 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (3539799/2500000000000:ℝ) ≤ wfun (x + y) := wc_259 (x + y) (by linarith) (by linarith)
                have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
                have hw5 : (1351302719/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_635 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (8559/8192:ℝ) with hc | hc
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_32 x (by linarith) (by linarith)
                have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (5211923/5000000000000:ℝ) ≤ wfun (x + y) := wc_253 (x + y) (by linarith) (by linarith)
                have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
                have hw5 : (1379579649/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_637 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (3539799/2500000000000:ℝ) ≤ wfun (x + y) := wc_259 (x + y) (by linarith) (by linarith)
                have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
                have hw5 : (1408130363/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_642 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total x (4277/4096:ℝ) with hc | hc
        · rcases le_total y (8109/4096:ℝ) with hc | hc
          · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
            have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_240 (x + y) (by linarith) (by linarith)
            have hw4 : (28027757/5000000000000:ℝ) ≤ wfun (y + z) := wc_285 (y + z) (by linarith) (by linarith)
            have hw5 : (660458559/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_629 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
            have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_250 (x + y) (by linarith) (by linarith)
            have hw4 : (18276411/2500000000000:ℝ) ≤ wfun (y + z) := wc_293 (y + z) (by linarith) (by linarith)
            have hw5 : (172136989/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_639 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (8109/4096:ℝ) with hc | hc
          · rcases le_total z (4307/4096:ℝ) with hc | hc
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
              have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_50 z (by linarith) (by linarith)
              have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_250 (x + y) (by linarith) (by linarith)
              have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
              have hw5 : (275750223/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_638 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
              have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_52 z (by linarith) (by linarith)
              have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_250 (x + y) (by linarith) (by linarith)
              have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
              have hw5 : (718045723/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_645 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (4307/4096:ℝ) with hc | hc
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
              have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_50 z (by linarith) (by linarith)
              have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_254 (x + y) (by linarith) (by linarith)
              have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
              have hw5 : (718045723/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_645 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
              have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_52 z (by linarith) (by linarith)
              have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_254 (x + y) (by linarith) (by linarith)
              have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
              have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_664 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total z (2151/2048:ℝ) with hc | hc
      · rcases le_total x (4277/4096:ℝ) with hc | hc
        · rcases le_total y (8119/4096:ℝ) with hc | hc
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · rcases le_total x (8549/8192:ℝ) with hc | hc
              · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_26 x (by linarith) (by linarith)
                have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (5211923/5000000000000:ℝ) ≤ wfun (x + y) := wc_253 (x + y) (by linarith) (by linarith)
                have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
                have hw5 : (1323300249/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_627 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_31 x (by linarith) (by linarith)
                have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (3539799/2500000000000:ℝ) ≤ wfun (x + y) := wc_259 (x + y) (by linarith) (by linarith)
                have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
                have hw5 : (1351302719/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_635 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
              have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_254 (x + y) (by linarith) (by linarith)
              have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
              have hw5 : (275750223/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_638 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · rcases le_total x (8549/8192:ℝ) with hc | hc
              · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_26 x (by linarith) (by linarith)
                have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (1846343/1000000000000:ℝ) ≤ wfun (x + y) := wc_261 (x + y) (by linarith) (by linarith)
                have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
                have hw5 : (1379579649/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_637 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_31 x (by linarith) (by linarith)
                have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (23335779/10000000000000:ℝ) ≤ wfun (x + y) := wc_265 (x + y) (by linarith) (by linarith)
                have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
                have hw5 : (1408130363/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_642 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
              have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_262 (x + y) (by linarith) (by linarith)
              have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
              have hw5 : (718045723/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_645 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (8119/4096:ℝ) with hc | hc
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · rcases le_total x (8559/8192:ℝ) with hc | hc
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_32 x (by linarith) (by linarith)
                have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (1846343/1000000000000:ℝ) ≤ wfun (x + y) := wc_261 (x + y) (by linarith) (by linarith)
                have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
                have hw5 : (1379579649/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_637 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (23335779/10000000000000:ℝ) ≤ wfun (x + y) := wc_265 (x + y) (by linarith) (by linarith)
                have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
                have hw5 : (1408130363/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_642 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (8559/8192:ℝ) with hc | hc
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_32 x (by linarith) (by linarith)
                have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (1846343/1000000000000:ℝ) ≤ wfun (x + y) := wc_261 (x + y) (by linarith) (by linarith)
                have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
                have hw5 : (718477089/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_644 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (23335779/10000000000000:ℝ) ≤ wfun (x + y) := wc_265 (x + y) (by linarith) (by linarith)
                have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
                have hw5 : (1466050409/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_661 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · rcases le_total x (8559/8192:ℝ) with hc | hc
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_32 x (by linarith) (by linarith)
                have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (28775469/10000000000000:ℝ) ≤ wfun (x + y) := wc_267 (x + y) (by linarith) (by linarith)
                have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
                have hw5 : (718477089/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_644 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (6956343/2000000000000:ℝ) ≤ wfun (x + y) := wc_275 (x + y) (by linarith) (by linarith)
                have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
                have hw5 : (1466050409/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_661 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (8559/8192:ℝ) with hc | hc
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_32 x (by linarith) (by linarith)
                have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (28775469/10000000000000:ℝ) ≤ wfun (x + y) := wc_267 (x + y) (by linarith) (by linarith)
                have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
                have hw5 : (1495418369/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_663 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (6956343/2000000000000:ℝ) ≤ wfun (x + y) := wc_275 (x + y) (by linarith) (by linarith)
                have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
                have hw5 : (1525057363/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_668 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total x (4277/4096:ℝ) with hc | hc
        · rcases le_total y (8119/4096:ℝ) with hc | hc
          · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
            have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_254 (x + y) (by linarith) (by linarith)
            have hw4 : (5774823/625000000000:ℝ) ≤ wfun (y + z) := wc_299 (y + z) (by linarith) (by linarith)
            have hw5 : (57374717/400000000000:ℝ) ≤ wfun (x + y + z) := wc_646 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
            have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_262 (x + y) (by linarith) (by linarith)
            have hw4 : (569617/50000000000:ℝ) ≤ wfun (y + z) := wc_316 (y + z) (by linarith) (by linarith)
            have hw5 : (1492727701/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_665 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (8119/4096:ℝ) with hc | hc
          · rcases le_total z (4307/4096:ℝ) with hc | hc
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
              have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_50 z (by linarith) (by linarith)
              have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_262 (x + y) (by linarith) (by linarith)
              have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
              have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_664 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
              have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_52 z (by linarith) (by linarith)
              have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_262 (x + y) (by linarith) (by linarith)
              have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_315 (y + z) (by linarith) (by linarith)
              have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_671 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (4307/4096:ℝ) with hc | hc
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
              have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_50 z (by linarith) (by linarith)
              have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_268 (x + y) (by linarith) (by linarith)
              have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_315 (y + z) (by linarith) (by linarith)
              have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_671 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
              have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_52 z (by linarith) (by linarith)
              have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_268 (x + y) (by linarith) (by linarith)
              have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_318 (y + z) (by linarith) (by linarith)
              have hw5 : (807312237/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_680 (x + y + z) (by linarith) (by linarith)
              linarith
  · rcases le_total y (4057/2048:ℝ) with hc | hc
    · rcases le_total z (2151/2048:ℝ) with hc | hc
      · rcases le_total x (4287/4096:ℝ) with hc | hc
        · rcases le_total y (8109/4096:ℝ) with hc | hc
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · rcases le_total x (8569/8192:ℝ) with hc | hc
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (5211923/5000000000000:ℝ) ≤ wfun (x + y) := wc_253 (x + y) (by linarith) (by linarith)
                have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_268 (y + z) (by linarith) (by linarith)
                have hw5 : (1323300249/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_627 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (3539799/2500000000000:ℝ) ≤ wfun (x + y) := wc_259 (x + y) (by linarith) (by linarith)
                have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_268 (y + z) (by linarith) (by linarith)
                have hw5 : (1351302719/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_635 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (8569/8192:ℝ) with hc | hc
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (5211923/5000000000000:ℝ) ≤ wfun (x + y) := wc_253 (x + y) (by linarith) (by linarith)
                have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
                have hw5 : (1379579649/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_637 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (3539799/2500000000000:ℝ) ≤ wfun (x + y) := wc_259 (x + y) (by linarith) (by linarith)
                have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
                have hw5 : (1408130363/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_642 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · rcases le_total x (8569/8192:ℝ) with hc | hc
              · rcases le_total y (16223/8192:ℝ) with hc | hc
                · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                  have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_107 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                  have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_260 (x + y) (by linarith) (by linarith)
                  have hw4 : (4135373/1000000000000:ℝ) ≤ wfun (y + z) := wc_277 (y + z) (by linarith) (by linarith)
                  have hw5 : (690204403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_636 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                  have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_109 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                  have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_264 (x + y) (by linarith) (by linarith)
                  have hw4 : (48490713/10000000000000:ℝ) ≤ wfun (y + z) := wc_281 (y + z) (by linarith) (by linarith)
                  have hw5 : (176122069/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_641 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (16223/8192:ℝ) with hc | hc
                · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                  have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_107 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                  have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_264 (x + y) (by linarith) (by linarith)
                  have hw4 : (4135373/1000000000000:ℝ) ≤ wfun (y + z) := wc_277 (y + z) (by linarith) (by linarith)
                  have hw5 : (176122069/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_641 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                  have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_109 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                  have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_266 (x + y) (by linarith) (by linarith)
                  have hw4 : (48490713/10000000000000:ℝ) ≤ wfun (y + z) := wc_281 (y + z) (by linarith) (by linarith)
                  have hw5 : (718908779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_643 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total x (8569/8192:ℝ) with hc | hc
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (1846343/1000000000000:ℝ) ≤ wfun (x + y) := wc_261 (x + y) (by linarith) (by linarith)
                have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
                have hw5 : (718477089/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_644 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (23335779/10000000000000:ℝ) ≤ wfun (x + y) := wc_265 (x + y) (by linarith) (by linarith)
                have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
                have hw5 : (1466050409/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_661 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total y (8109/4096:ℝ) with hc | hc
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · rcases le_total x (8579/8192:ℝ) with hc | hc
              · rcases le_total y (16213/8192:ℝ) with hc | hc
                · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                  have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_101 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                  have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_260 (x + y) (by linarith) (by linarith)
                  have hw4 : (28775469/10000000000000:ℝ) ≤ wfun (y + z) := wc_267 (y + z) (by linarith) (by linarith)
                  have hw5 : (690204403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_636 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                  have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_106 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                  have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_264 (x + y) (by linarith) (by linarith)
                  have hw4 : (6956343/2000000000000:ℝ) ≤ wfun (y + z) := wc_275 (y + z) (by linarith) (by linarith)
                  have hw5 : (176122069/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_641 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (23335779/10000000000000:ℝ) ≤ wfun (x + y) := wc_265 (x + y) (by linarith) (by linarith)
                have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_268 (y + z) (by linarith) (by linarith)
                have hw5 : (1408130363/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_642 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (8579/8192:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (1846343/1000000000000:ℝ) ≤ wfun (x + y) := wc_261 (x + y) (by linarith) (by linarith)
                have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
                have hw5 : (718477089/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_644 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (23335779/10000000000000:ℝ) ≤ wfun (x + y) := wc_265 (x + y) (by linarith) (by linarith)
                have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
                have hw5 : (1466050409/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_661 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · rcases le_total x (8579/8192:ℝ) with hc | hc
              · rcases le_total y (16223/8192:ℝ) with hc | hc
                · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                  have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_107 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                  have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_266 (x + y) (by linarith) (by linarith)
                  have hw4 : (4135373/1000000000000:ℝ) ≤ wfun (y + z) := wc_277 (y + z) (by linarith) (by linarith)
                  have hw5 : (718908779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_643 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                  have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_109 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                  have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_274 (x + y) (by linarith) (by linarith)
                  have hw4 : (48490713/10000000000000:ℝ) ≤ wfun (y + z) := wc_281 (y + z) (by linarith) (by linarith)
                  have hw5 : (1466931139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_660 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (16223/8192:ℝ) with hc | hc
                · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                  have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_107 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                  have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_274 (x + y) (by linarith) (by linarith)
                  have hw4 : (4135373/1000000000000:ℝ) ≤ wfun (y + z) := wc_277 (y + z) (by linarith) (by linarith)
                  have hw5 : (1466931139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_660 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                  have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_109 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                  have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_276 (x + y) (by linarith) (by linarith)
                  have hw4 : (48490713/10000000000000:ℝ) ≤ wfun (y + z) := wc_281 (y + z) (by linarith) (by linarith)
                  have hw5 : (748158303/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_662 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total x (8579/8192:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (28775469/10000000000000:ℝ) ≤ wfun (x + y) := wc_267 (x + y) (by linarith) (by linarith)
                have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
                have hw5 : (1495418369/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_663 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (6956343/2000000000000:ℝ) ≤ wfun (x + y) := wc_275 (x + y) (by linarith) (by linarith)
                have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
                have hw5 : (1525057363/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_668 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total x (4287/4096:ℝ) with hc | hc
        · rcases le_total y (8109/4096:ℝ) with hc | hc
          · rcases le_total z (4307/4096:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
              have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_50 z (by linarith) (by linarith)
              have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_254 (x + y) (by linarith) (by linarith)
              have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
              have hw5 : (718045723/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_645 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
              have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_52 z (by linarith) (by linarith)
              have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_254 (x + y) (by linarith) (by linarith)
              have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
              have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_664 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (4307/4096:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
              have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_50 z (by linarith) (by linarith)
              have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_262 (x + y) (by linarith) (by linarith)
              have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
              have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_664 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
              have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_52 z (by linarith) (by linarith)
              have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_262 (x + y) (by linarith) (by linarith)
              have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
              have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_671 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (8109/4096:ℝ) with hc | hc
          · rcases le_total z (4307/4096:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_50 z (by linarith) (by linarith)
              have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_262 (x + y) (by linarith) (by linarith)
              have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
              have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_664 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_52 z (by linarith) (by linarith)
              have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_262 (x + y) (by linarith) (by linarith)
              have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
              have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_671 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (4307/4096:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_50 z (by linarith) (by linarith)
              have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_268 (x + y) (by linarith) (by linarith)
              have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
              have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_671 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_52 z (by linarith) (by linarith)
              have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_268 (x + y) (by linarith) (by linarith)
              have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
              have hw5 : (807312237/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_680 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total z (2151/2048:ℝ) with hc | hc
      · rcases le_total x (4287/4096:ℝ) with hc | hc
        · rcases le_total y (8119/4096:ℝ) with hc | hc
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · rcases le_total x (8569/8192:ℝ) with hc | hc
              · rcases le_total y (16233/8192:ℝ) with hc | hc
                · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                  have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_110 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                  have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_266 (x + y) (by linarith) (by linarith)
                  have hw4 : (2809593/500000000000:ℝ) ≤ wfun (y + z) := wc_283 (y + z) (by linarith) (by linarith)
                  have hw5 : (718908779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_643 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                  have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_113 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                  have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_274 (x + y) (by linarith) (by linarith)
                  have hw4 : (64456359/10000000000000:ℝ) ≤ wfun (y + z) := wc_289 (y + z) (by linarith) (by linarith)
                  have hw5 : (1466931139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_660 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (16233/8192:ℝ) with hc | hc
                · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                  have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_110 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                  have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_274 (x + y) (by linarith) (by linarith)
                  have hw4 : (2809593/500000000000:ℝ) ≤ wfun (y + z) := wc_283 (y + z) (by linarith) (by linarith)
                  have hw5 : (1466931139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_660 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                  have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_113 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                  have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_276 (x + y) (by linarith) (by linarith)
                  have hw4 : (64456359/10000000000000:ℝ) ≤ wfun (y + z) := wc_289 (y + z) (by linarith) (by linarith)
                  have hw5 : (748158303/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_662 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total x (8569/8192:ℝ) with hc | hc
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (28775469/10000000000000:ℝ) ≤ wfun (x + y) := wc_267 (x + y) (by linarith) (by linarith)
                have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
                have hw5 : (1495418369/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_663 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (6956343/2000000000000:ℝ) ≤ wfun (x + y) := wc_275 (x + y) (by linarith) (by linarith)
                have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
                have hw5 : (1525057363/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_668 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · rcases le_total x (8569/8192:ℝ) with hc | hc
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (4135373/1000000000000:ℝ) ≤ wfun (x + y) := wc_277 (x + y) (by linarith) (by linarith)
                have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
                have hw5 : (1495418369/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_663 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total y (16243/8192:ℝ) with hc | hc
                · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                  have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_114 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                  have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_280 (x + y) (by linarith) (by linarith)
                  have hw4 : (73283389/10000000000000:ℝ) ≤ wfun (y + z) := wc_291 (y + z) (by linarith) (by linarith)
                  have hw5 : (305194653/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_667 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                  have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_116 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                  have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_282 (x + y) (by linarith) (by linarith)
                  have hw4 : (82672123/10000000000000:ℝ) ≤ wfun (y + z) := wc_295 (y + z) (by linarith) (by linarith)
                  have hw5 : (77795021/500000000000:ℝ) ≤ wfun (x + y + z) := wc_669 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total x (8569/8192:ℝ) with hc | hc
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (4135373/1000000000000:ℝ) ≤ wfun (x + y) := wc_277 (x + y) (by linarith) (by linarith)
                have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
                have hw5 : (194370837/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_670 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (48490713/10000000000000:ℝ) ≤ wfun (x + y) := wc_281 (x + y) (by linarith) (by linarith)
                have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
                have hw5 : (1585145671/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_678 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total y (8119/4096:ℝ) with hc | hc
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · rcases le_total x (8579/8192:ℝ) with hc | hc
              · rcases le_total y (16233/8192:ℝ) with hc | hc
                · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                  have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_110 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                  have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_276 (x + y) (by linarith) (by linarith)
                  have hw4 : (2809593/500000000000:ℝ) ≤ wfun (y + z) := wc_283 (y + z) (by linarith) (by linarith)
                  have hw5 : (748158303/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_662 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                  have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_113 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                  have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_280 (x + y) (by linarith) (by linarith)
                  have hw4 : (64456359/10000000000000:ℝ) ≤ wfun (y + z) := wc_289 (y + z) (by linarith) (by linarith)
                  have hw5 : (305194653/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_667 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (16233/8192:ℝ) with hc | hc
                · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                  have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_110 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                  have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_280 (x + y) (by linarith) (by linarith)
                  have hw4 : (2809593/500000000000:ℝ) ≤ wfun (y + z) := wc_283 (y + z) (by linarith) (by linarith)
                  have hw5 : (305194653/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_667 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                  have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_113 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                  have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_282 (x + y) (by linarith) (by linarith)
                  have hw4 : (64456359/10000000000000:ℝ) ≤ wfun (y + z) := wc_289 (y + z) (by linarith) (by linarith)
                  have hw5 : (77795021/500000000000:ℝ) ≤ wfun (x + y + z) := wc_669 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total x (8579/8192:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (4135373/1000000000000:ℝ) ≤ wfun (x + y) := wc_277 (x + y) (by linarith) (by linarith)
                have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
                have hw5 : (194370837/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_670 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (48490713/10000000000000:ℝ) ≤ wfun (x + y) := wc_281 (x + y) (by linarith) (by linarith)
                have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
                have hw5 : (1585145671/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_678 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · rcases le_total x (8579/8192:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (2809593/500000000000:ℝ) ≤ wfun (x + y) := wc_283 (x + y) (by linarith) (by linarith)
                have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
                have hw5 : (194370837/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_670 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (64456359/10000000000000:ℝ) ≤ wfun (x + y) := wc_289 (x + y) (by linarith) (by linarith)
                have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
                have hw5 : (1585145671/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_678 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (8579/8192:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (2809593/500000000000:ℝ) ≤ wfun (x + y) := wc_283 (x + y) (by linarith) (by linarith)
                have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
                have hw5 : (100974599/625000000000:ℝ) ≤ wfun (x + y + z) := wc_679 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (64456359/10000000000000:ℝ) ≤ wfun (x + y) := wc_289 (x + y) (by linarith) (by linarith)
                have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
                have hw5 : (51447179/312500000000:ℝ) ≤ wfun (x + y + z) := wc_683 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total x (4287/4096:ℝ) with hc | hc
        · rcases le_total y (8119/4096:ℝ) with hc | hc
          · rcases le_total z (4307/4096:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
              have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_50 z (by linarith) (by linarith)
              have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_268 (x + y) (by linarith) (by linarith)
              have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
              have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_671 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
              have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_52 z (by linarith) (by linarith)
              have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_268 (x + y) (by linarith) (by linarith)
              have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_315 (y + z) (by linarith) (by linarith)
              have hw5 : (807312237/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_680 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (4307/4096:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
              have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_50 z (by linarith) (by linarith)
              have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_278 (x + y) (by linarith) (by linarith)
              have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_315 (y + z) (by linarith) (by linarith)
              have hw5 : (807312237/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_680 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
              have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_52 z (by linarith) (by linarith)
              have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_278 (x + y) (by linarith) (by linarith)
              have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_318 (y + z) (by linarith) (by linarith)
              have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_685 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (8119/4096:ℝ) with hc | hc
          · rcases le_total z (4307/4096:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_50 z (by linarith) (by linarith)
              have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_278 (x + y) (by linarith) (by linarith)
              have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
              have hw5 : (807312237/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_680 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_52 z (by linarith) (by linarith)
              have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_278 (x + y) (by linarith) (by linarith)
              have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_315 (y + z) (by linarith) (by linarith)
              have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_685 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (4307/4096:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_50 z (by linarith) (by linarith)
              have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_284 (x + y) (by linarith) (by linarith)
              have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_315 (y + z) (by linarith) (by linarith)
              have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_685 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_52 z (by linarith) (by linarith)
              have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_284 (x + y) (by linarith) (by linarith)
              have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_318 (y + z) (by linarith) (by linarith)
              have hw5 : (1739017297/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_696 (x + y + z) (by linarith) (by linarith)
              linarith

set_option maxHeartbeats 20000000 in
lemma ch_47 (x y z : ℝ) (hx1 : (131/128:ℝ) ≤ x) (hx2 : x ≤ (17/16:ℝ))
    (hy1 : (257/128:ℝ) ≤ y) (hy2 : y ≤ (131/64:ℝ))
    (hz1 : (63/64:ℝ) ≤ z) (hz2 : z ≤ (17/16:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total z (131/128:ℝ) with hc | hc
  · rcases le_total x (267/256:ℝ) with hc | hc
    · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
      have hw2 : (2370342229/2500000000000:ℝ) ≤ wfun z := by
        rcases le_total z (1:ℝ) with hq20 | hq20
        · exact le_trans (by norm_num) (wc_5 z (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_7 z (by linarith) (by linarith))
      have hw3 : (21491553/2500000000000:ℝ) ≤ wfun (x + y) := wc_307 (x + y) (by linarith) (by linarith)
      have hw5 : (59421/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_457 (x + y + z) (by linarith) (by linarith)
      linarith
    · have hw2 : (2370342229/2500000000000:ℝ) ≤ wfun z := by
        rcases le_total z (1:ℝ) with hq20 | hq20
        · exact le_trans (by norm_num) (wc_5 z (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_7 z (by linarith) (by linarith))
      have hw3 : (162913869/2500000000000:ℝ) ≤ wfun (x + y) := wc_360 (x + y) (by linarith) (by linarith)
      have hw5 : (153865963/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_514 (x + y + z) (by linarith) (by linarith)
      linarith
  · rcases le_total x (267/256:ℝ) with hc | hc
    · rcases le_total y (519/256:ℝ) with hc | hc
      · rcases le_total z (267/256:ℝ) with hc | hc
        · rcases le_total x (529/512:ℝ) with hc | hc
          · rcases le_total y (1033/512:ℝ) with hc | hc
            · rcases le_total z (529/512:ℝ) with hc | hc
              · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
                have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
                have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
                have hw3 : (18095851/2000000000000:ℝ) ≤ wfun (x + y) := wc_304 (x + y) (by linarith) (by linarith)
                have hw4 : (18095851/2000000000000:ℝ) ≤ wfun (y + z) := wc_304 (y + z) (by linarith) (by linarith)
                have hw5 : (636617867/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_548 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total x (1053/1024:ℝ) with hc | hc
                · have hw0 : (3436255003/5000000000000:ℝ) ≤ wfun x := wc_11 x (by linarith) (by linarith)
                  have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
                  have hw3 : (91064031/10000000000000:ℝ) ≤ wfun (x + y) := wc_303 (x + y) (by linarith) (by linarith)
                  have hw4 : (63967043/2000000000000:ℝ) ≤ wfun (y + z) := wc_344 (y + z) (by linarith) (by linarith)
                  have hw5 : (197587481/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_586 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_14 x (by linarith) (by linarith)
                  have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
                  have hw3 : (189078223/10000000000000:ℝ) ≤ wfun (x + y) := wc_329 (x + y) (by linarith) (by linarith)
                  have hw4 : (63967043/2000000000000:ℝ) ≤ wfun (y + z) := wc_344 (y + z) (by linarith) (by linarith)
                  have hw5 : (74301831/625000000000:ℝ) ≤ wfun (x + y + z) := wc_615 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total z (529/512:ℝ) with hc | hc
              · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
                have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
                have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
                have hw3 : (63967043/2000000000000:ℝ) ≤ wfun (x + y) := wc_344 (x + y) (by linarith) (by linarith)
                have hw4 : (63967043/2000000000000:ℝ) ≤ wfun (y + z) := wc_344 (y + z) (by linarith) (by linarith)
                have hw5 : (49160907/500000000000:ℝ) ≤ wfun (x + y + z) := wc_587 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
                have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
                have hw3 : (63967043/2000000000000:ℝ) ≤ wfun (x + y) := wc_344 (x + y) (by linarith) (by linarith)
                have hw4 : (685641829/10000000000000:ℝ) ≤ wfun (y + z) := wc_356 (y + z) (by linarith) (by linarith)
                have hw5 : (140043451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_654 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (1033/512:ℝ) with hc | hc
            · rcases le_total z (529/512:ℝ) with hc | hc
              · rcases le_total x (1063/1024:ℝ) with hc | hc
                · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_16 x (by linarith) (by linarith)
                  have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
                  have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
                  have hw3 : (160947823/5000000000000:ℝ) ≤ wfun (x + y) := wc_343 (x + y) (by linarith) (by linarith)
                  have hw4 : (18095851/2000000000000:ℝ) ≤ wfun (y + z) := wc_304 (y + z) (by linarith) (by linarith)
                  have hw5 : (197587481/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_586 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
                  have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
                  have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
                  have hw3 : (489049523/10000000000000:ℝ) ≤ wfun (x + y) := wc_351 (x + y) (by linarith) (by linarith)
                  have hw4 : (18095851/2000000000000:ℝ) ≤ wfun (y + z) := wc_304 (y + z) (by linarith) (by linarith)
                  have hw5 : (74301831/625000000000:ℝ) ≤ wfun (x + y + z) := wc_615 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total x (1063/1024:ℝ) with hc | hc
                · rcases le_total y (2061/1024:ℝ) with hc | hc
                  · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_16 x (by linarith) (by linarith)
                    have hw1 : (543159341/10000000000000:ℝ) ≤ wfun y := wc_144 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
                    have hw3 : (161986357/5000000000000:ℝ) ≤ wfun (x + y) := wc_342 (x + y) (by linarith) (by linarith)
                    have hw4 : (160947823/5000000000000:ℝ) ≤ wfun (y + z) := wc_343 (y + z) (by linarith) (by linarith)
                    have hw5 : (1413886087/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_652 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_16 x (by linarith) (by linarith)
                    have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
                    have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_350 (x + y) (by linarith) (by linarith)
                    have hw4 : (489049523/10000000000000:ℝ) ≤ wfun (y + z) := wc_351 (y + z) (by linarith) (by linarith)
                    have hw5 : (12893743/78125000000:ℝ) ≤ wfun (x + y + z) := wc_692 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total y (2061/1024:ℝ) with hc | hc
                  · rcases le_total z (1063/1024:ℝ) with hc | hc
                    · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
                      have hw1 : (543159341/10000000000000:ℝ) ≤ wfun y := wc_144 y (by linarith) (by linarith)
                      have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
                      have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_350 (x + y) (by linarith) (by linarith)
                      have hw4 : (161986357/5000000000000:ℝ) ≤ wfun (y + z) := wc_342 (y + z) (by linarith) (by linarith)
                      have hw5 : (1658311191/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_691 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
                      have hw1 : (543159341/10000000000000:ℝ) ≤ wfun y := wc_144 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
                      have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_350 (x + y) (by linarith) (by linarith)
                      have hw4 : (24610003/500000000000:ℝ) ≤ wfun (y + z) := wc_350 (y + z) (by linarith) (by linarith)
                      have hw5 : (1912837973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_713 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
                    have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
                    have hw3 : (694482783/10000000000000:ℝ) ≤ wfun (x + y) := wc_354 (x + y) (by linarith) (by linarith)
                    have hw4 : (489049523/10000000000000:ℝ) ≤ wfun (y + z) := wc_351 (y + z) (by linarith) (by linarith)
                    have hw5 : (951861201/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_714 (x + y + z) (by linarith) (by linarith)
                    linarith
            · rcases le_total z (529/512:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
                have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
                have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
                have hw3 : (685641829/10000000000000:ℝ) ≤ wfun (x + y) := wc_356 (x + y) (by linarith) (by linarith)
                have hw4 : (63967043/2000000000000:ℝ) ≤ wfun (y + z) := wc_344 (y + z) (by linarith) (by linarith)
                have hw5 : (140043451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_654 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
                have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
                have hw3 : (685641829/10000000000000:ℝ) ≤ wfun (x + y) := wc_356 (x + y) (by linarith) (by linarith)
                have hw4 : (685641829/10000000000000:ℝ) ≤ wfun (y + z) := wc_356 (y + z) (by linarith) (by linarith)
                have hw5 : (942826837/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_716 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (529/512:ℝ) with hc | hc
          · rcases le_total y (1033/512:ℝ) with hc | hc
            · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
              have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
              have hw3 : (18095851/2000000000000:ℝ) ≤ wfun (x + y) := wc_304 (x + y) (by linarith) (by linarith)
              have hw4 : (676941261/10000000000000:ℝ) ≤ wfun (y + z) := wc_357 (y + z) (by linarith) (by linarith)
              have hw5 : (69357131/500000000000:ℝ) ≤ wfun (x + y + z) := wc_655 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
              have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw3 : (63967043/2000000000000:ℝ) ≤ wfun (x + y) := wc_344 (x + y) (by linarith) (by linarith)
              have hw4 : (1168886057/10000000000000:ℝ) ≤ wfun (y + z) := wc_366 (y + z) (by linarith) (by linarith)
              have hw5 : (933899467/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_717 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (1033/512:ℝ) with hc | hc
            · rcases le_total z (539/512:ℝ) with hc | hc
              · rcases le_total x (1063/1024:ℝ) with hc | hc
                · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_16 x (by linarith) (by linarith)
                  have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
                  have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                  have hw3 : (160947823/5000000000000:ℝ) ≤ wfun (x + y) := wc_343 (x + y) (by linarith) (by linarith)
                  have hw4 : (685641829/10000000000000:ℝ) ≤ wfun (y + z) := wc_356 (y + z) (by linarith) (by linarith)
                  have hw5 : (947330549/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_715 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
                  have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
                  have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                  have hw3 : (489049523/10000000000000:ℝ) ≤ wfun (x + y) := wc_351 (x + y) (by linarith) (by linarith)
                  have hw4 : (685641829/10000000000000:ℝ) ≤ wfun (y + z) := wc_356 (y + z) (by linarith) (by linarith)
                  have hw5 : (216315697/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_730 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
                have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
                have hw3 : (63967043/2000000000000:ℝ) ≤ wfun (x + y) := wc_344 (x + y) (by linarith) (by linarith)
                have hw4 : (591930551/5000000000000:ℝ) ≤ wfun (y + z) := wc_365 (y + z) (by linarith) (by linarith)
                have hw5 : (1218017847/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_736 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
              have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw3 : (685641829/10000000000000:ℝ) ≤ wfun (x + y) := wc_356 (x + y) (by linarith) (by linarith)
              have hw4 : (1168886057/10000000000000:ℝ) ≤ wfun (y + z) := wc_366 (y + z) (by linarith) (by linarith)
              have hw5 : (2413024171/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_737 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (267/256:ℝ) with hc | hc
        · rcases le_total x (529/512:ℝ) with hc | hc
          · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
            have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_13 z (by linarith) (by linarith)
            have hw3 : (676941261/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
            have hw4 : (66837841/1000000000000:ℝ) ≤ wfun (y + z) := wc_358 (y + z) (by linarith) (by linarith)
            have hw5 : (274801629/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_656 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
            have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_13 z (by linarith) (by linarith)
            have hw3 : (1168886057/10000000000000:ℝ) ≤ wfun (x + y) := wc_366 (x + y) (by linarith) (by linarith)
            have hw4 : (66837841/1000000000000:ℝ) ≤ wfun (y + z) := wc_358 (y + z) (by linarith) (by linarith)
            have hw5 : (1850155147/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_718 (x + y + z) (by linarith) (by linarith)
            linarith
        · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
          have hw3 : (66837841/1000000000000:ℝ) ≤ wfun (x + y) := wc_358 (x + y) (by linarith) (by linarith)
          have hw4 : (1764735511/10000000000000:ℝ) ≤ wfun (y + z) := wc_370 (y + z) (by linarith) (by linarith)
          have hw5 : (591952751/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_738 (x + y + z) (by linarith) (by linarith)
          linarith
    · rcases le_total y (519/256:ℝ) with hc | hc
      · rcases le_total z (267/256:ℝ) with hc | hc
        · rcases le_total x (539/512:ℝ) with hc | hc
          · rcases le_total y (1033/512:ℝ) with hc | hc
            · rcases le_total z (529/512:ℝ) with hc | hc
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
                have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
                have hw3 : (685641829/10000000000000:ℝ) ≤ wfun (x + y) := wc_356 (x + y) (by linarith) (by linarith)
                have hw4 : (18095851/2000000000000:ℝ) ≤ wfun (y + z) := wc_304 (y + z) (by linarith) (by linarith)
                have hw5 : (140043451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_654 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total x (1073/1024:ℝ) with hc | hc
                · rcases le_total y (2061/1024:ℝ) with hc | hc
                  · rcases le_total z (1063/1024:ℝ) with hc | hc
                    · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                      have hw1 : (543159341/10000000000000:ℝ) ≤ wfun y := wc_144 y (by linarith) (by linarith)
                      have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
                      have hw3 : (694482783/10000000000000:ℝ) ≤ wfun (x + y) := wc_354 (x + y) (by linarith) (by linarith)
                      have hw4 : (161986357/5000000000000:ℝ) ≤ wfun (y + z) := wc_342 (y + z) (by linarith) (by linarith)
                      have hw5 : (1912837973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_713 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                      have hw1 : (543159341/10000000000000:ℝ) ≤ wfun y := wc_144 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
                      have hw3 : (694482783/10000000000000:ℝ) ≤ wfun (x + y) := wc_354 (x + y) (by linarith) (by linarith)
                      have hw4 : (24610003/500000000000:ℝ) ≤ wfun (y + z) := wc_350 (y + z) (by linarith) (by linarith)
                      have hw5 : (272985599/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_728 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                    have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
                    have hw3 : (930293373/10000000000000:ℝ) ≤ wfun (x + y) := wc_362 (x + y) (by linarith) (by linarith)
                    have hw4 : (489049523/10000000000000:ℝ) ≤ wfun (y + z) := wc_351 (y + z) (by linarith) (by linarith)
                    have hw5 : (271686247/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_729 (x + y + z) (by linarith) (by linarith)
                    linarith
                · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                  have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
                  have hw3 : (924357731/10000000000000:ℝ) ≤ wfun (x + y) := wc_363 (x + y) (by linarith) (by linarith)
                  have hw4 : (63967043/2000000000000:ℝ) ≤ wfun (y + z) := wc_344 (y + z) (by linarith) (by linarith)
                  have hw5 : (216315697/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_730 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total z (529/512:ℝ) with hc | hc
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
                have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
                have hw3 : (591930551/5000000000000:ℝ) ≤ wfun (x + y) := wc_365 (x + y) (by linarith) (by linarith)
                have hw4 : (63967043/2000000000000:ℝ) ≤ wfun (y + z) := wc_344 (y + z) (by linarith) (by linarith)
                have hw5 : (942826837/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_716 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
                have hw3 : (591930551/5000000000000:ℝ) ≤ wfun (x + y) := wc_365 (x + y) (by linarith) (by linarith)
                have hw4 : (685641829/10000000000000:ℝ) ≤ wfun (y + z) := wc_356 (y + z) (by linarith) (by linarith)
                have hw5 : (1218017847/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_736 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (1033/512:ℝ) with hc | hc
            · rcases le_total z (529/512:ℝ) with hc | hc
              · have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
                have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
                have hw3 : (591930551/5000000000000:ℝ) ≤ wfun (x + y) := wc_365 (x + y) (by linarith) (by linarith)
                have hw4 : (18095851/2000000000000:ℝ) ≤ wfun (y + z) := wc_304 (y + z) (by linarith) (by linarith)
                have hw5 : (942826837/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_716 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
                have hw3 : (591930551/5000000000000:ℝ) ≤ wfun (x + y) := wc_365 (x + y) (by linarith) (by linarith)
                have hw4 : (63967043/2000000000000:ℝ) ≤ wfun (y + z) := wc_344 (y + z) (by linarith) (by linarith)
                have hw5 : (1218017847/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_736 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_13 z (by linarith) (by linarith)
              have hw3 : (1810022563/10000000000000:ℝ) ≤ wfun (x + y) := wc_369 (x + y) (by linarith) (by linarith)
              have hw4 : (157881813/5000000000000:ℝ) ≤ wfun (y + z) := wc_345 (y + z) (by linarith) (by linarith)
              have hw5 : (2413024171/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_737 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (539/512:ℝ) with hc | hc
          · rcases le_total y (1033/512:ℝ) with hc | hc
            · rcases le_total z (539/512:ℝ) with hc | hc
              · rcases le_total x (1073/1024:ℝ) with hc | hc
                · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                  have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
                  have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                  have hw3 : (172511147/2500000000000:ℝ) ≤ wfun (x + y) := wc_355 (x + y) (by linarith) (by linarith)
                  have hw4 : (685641829/10000000000000:ℝ) ≤ wfun (y + z) := wc_356 (y + z) (by linarith) (by linarith)
                  have hw5 : (2447644383/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_735 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                  have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
                  have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                  have hw3 : (924357731/10000000000000:ℝ) ≤ wfun (x + y) := wc_363 (x + y) (by linarith) (by linarith)
                  have hw4 : (685641829/10000000000000:ℝ) ≤ wfun (y + z) := wc_356 (y + z) (by linarith) (by linarith)
                  have hw5 : (549546581/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_744 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
                have hw3 : (685641829/10000000000000:ℝ) ≤ wfun (x + y) := wc_356 (x + y) (by linarith) (by linarith)
                have hw4 : (591930551/5000000000000:ℝ) ≤ wfun (y + z) := wc_365 (y + z) (by linarith) (by linarith)
                have hw5 : (3048526697/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_746 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
              have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw3 : (591930551/5000000000000:ℝ) ≤ wfun (x + y) := wc_365 (x + y) (by linarith) (by linarith)
              have hw4 : (1168886057/10000000000000:ℝ) ≤ wfun (y + z) := wc_366 (y + z) (by linarith) (by linarith)
              have hw5 : (3019797449/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_747 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
            have hw3 : (1168886057/10000000000000:ℝ) ≤ wfun (x + y) := wc_366 (x + y) (by linarith) (by linarith)
            have hw4 : (66837841/1000000000000:ℝ) ≤ wfun (y + z) := wc_358 (y + z) (by linarith) (by linarith)
            have hw5 : (2991406031/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_748 (x + y + z) (by linarith) (by linarith)
            linarith
      · have hw3 : (1764735511/10000000000000:ℝ) ≤ wfun (x + y) := wc_370 (x + y) (by linarith) (by linarith)
        have hw4 : (162913869/2500000000000:ℝ) ≤ wfun (y + z) := wc_360 (y + z) (by linarith) (by linarith)
        have hw5 : (1161826227/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_739 (x + y + z) (by linarith) (by linarith)
        linarith

set_option maxHeartbeats 20000000 in
lemma ch_72 (x y z : ℝ) (hx1 : (121/64:ℝ) ≤ x) (hx2 : x ≤ (131/64:ℝ))
    (hy1 : (63/64:ℝ) ≤ y) (hy2 : y ≤ (73/64:ℝ))
    (hz1 : (131/64:ℝ) ≤ z) (hz2 : z ≤ (141/64:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (63/32:ℝ) with hc | hc
  · have hw0 : (795663039/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
    have hw2 : (182240171/5000000000000:ℝ) ≤ wfun z := wc_160 z (by linarith) (by linarith)
    have hw4 : (17540223/2500000000000:ℝ) ≤ wfun (y + z) := by
      rcases le_total (y + z) (13/4:ℝ) with hq40 | hq40
      · exact le_trans (by norm_num) (wc_312 (y + z) (by linarith) (by linarith))
      exact le_trans (by norm_num) (wc_392 (y + z) (by linarith) (by linarith))
    linarith
  · rcases le_total y (17/16:ℝ) with hc | hc
    · rcases le_total z (17/8:ℝ) with hc | hc
      · rcases le_total x (257/128:ℝ) with hc | hc
        · rcases le_total y (131/128:ℝ) with hc | hc
          · have hw0 : (179073511/2000000000000:ℝ) ≤ wfun x := by
              rcases le_total x (2:ℝ) with hq00 | hq00
              · exact le_trans (by norm_num) (wc_90 x (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_141 x (by linarith) (by linarith))
            have hw1 : (2370342229/2500000000000:ℝ) ≤ wfun y := by
              rcases le_total y (1:ℝ) with hq10 | hq10
              · exact le_trans (by norm_num) (wc_5 y (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_7 y (by linarith) (by linarith))
            have hw2 : (42177537/1000000000000:ℝ) ≤ wfun z := wc_158 z (by linarith) (by linarith)
            have hw4 : (79711817/10000000000000:ℝ) ≤ wfun (y + z) := wc_310 (y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total z (267/128:ℝ) with hc | hc
            · rcases le_total x (509/256:ℝ) with hc | hc
              · have hw0 : (396477691/1250000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
                have hw2 : (18186303/400000000000:ℝ) ≤ wfun z := wc_156 z (by linarith) (by linarith)
                have hw4 : (419583999/2500000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
                have hw5 : (90750063/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_812 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (179073511/2000000000000:ℝ) ≤ wfun x := by
                  rcases le_total x (2:ℝ) with hq00 | hq00
                  · exact le_trans (by norm_num) (wc_130 x (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_141 x (by linarith) (by linarith))
                have hw2 : (18186303/400000000000:ℝ) ≤ wfun z := wc_156 z (by linarith) (by linarith)
                have hw4 : (419583999/2500000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
                have hw5 : (534939039/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_885 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (179073511/2000000000000:ℝ) ≤ wfun x := by
                rcases le_total x (2:ℝ) with hq00 | hq00
                · exact le_trans (by norm_num) (wc_90 x (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_141 x (by linarith) (by linarith))
              have hw2 : (4789633321/10000000000000:ℝ) ≤ wfun z := wc_172 z (by linarith) (by linarith)
              have hw4 : (5096134953/10000000000000:ℝ) ≤ wfun (y + z) := wc_384 (y + z) (by linarith) (by linarith)
              have hw5 : (1048517003/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_949 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (131/128:ℝ) with hc | hc
          · have hw1 : (2370342229/2500000000000:ℝ) ≤ wfun y := by
              rcases le_total y (1:ℝ) with hq10 | hq10
              · exact le_trans (by norm_num) (wc_5 y (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_7 y (by linarith) (by linarith))
            have hw2 : (42177537/1000000000000:ℝ) ≤ wfun z := wc_158 z (by linarith) (by linarith)
            have hw4 : (79711817/10000000000000:ℝ) ≤ wfun (y + z) := wc_310 (y + z) (by linarith) (by linarith)
            have hw5 : (21679333/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_813 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw2 : (42177537/1000000000000:ℝ) ≤ wfun z := wc_158 z (by linarith) (by linarith)
            have hw3 : (20953831/2500000000000:ℝ) ≤ wfun (x + y) := wc_308 (x + y) (by linarith) (by linarith)
            have hw4 : (798582451/5000000000000:ℝ) ≤ wfun (y + z) := wc_374 (y + z) (by linarith) (by linarith)
            have hw5 : (1017509707/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_950 (x + y + z) (by linarith) (by linarith)
            linarith
      · have hw2 : (48584483/40000000000:ℝ) ≤ wfun z := wc_178 z (by linarith) (by linarith)
        have hw4 : (589186081/1250000000000:ℝ) ≤ wfun (y + z) := by
          rcases le_total (y + z) (13/4:ℝ) with hq40 | hq40
          · exact le_trans (by norm_num) (wc_386 (y + z) (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_389 (y + z) (by linarith) (by linarith))
        have hw5 : (502714163/5000000000000:ℝ) ≤ wfun (x + y + z) := by
          rcases le_total (x + y + z) (21/4:ℝ) with hq50 | hq50
          · exact le_trans (by norm_num) (wc_951 (x + y + z) (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_974 (x + y + z) (by linarith) (by linarith))
        linarith
    · have hw1 : (15429929/1000000000000:ℝ) ≤ wfun y := wc_63 y (by linarith) (by linarith)
      have hw2 : (182240171/5000000000000:ℝ) ≤ wfun z := wc_160 z (by linarith) (by linarith)
      have hw3 : (75856633/10000000000000:ℝ) ≤ wfun (x + y) := wc_311 (x + y) (by linarith) (by linarith)
      have hw4 : (589186081/1250000000000:ℝ) ≤ wfun (y + z) := by
        rcases le_total (y + z) (13/4:ℝ) with hq40 | hq40
        · exact le_trans (by norm_num) (wc_386 (y + z) (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_392 (y + z) (by linarith) (by linarith))
      have hw5 : (502714163/5000000000000:ℝ) ≤ wfun (x + y + z) := by
        rcases le_total (x + y + z) (21/4:ℝ) with hq50 | hq50
        · exact le_trans (by norm_num) (wc_951 (x + y + z) (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_977 (x + y + z) (by linarith) (by linarith))
      linarith

end Zeta23Ext.Bridge.FourPoint
