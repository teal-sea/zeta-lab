import FourPoint.Cells

/-! Chunk module 6 of 16 of the three-dimensional table.  Each lemma is one
subtree of at most 110 leaves of one box's bisection tree; `FourPoint/Boxes.lean` routes
the box down to them.  Cutting the tree this way gives each subtree its own
heartbeat budget and lets `lake` compile them in parallel. -/

noncomputable section
namespace Zeta23Ext.Bridge.FourPoint

set_option maxHeartbeats 20000000 in
lemma ch_9 (x y z : ℝ) (hx1 : (529/512:ℝ) ≤ x) (hx2 : x ≤ (267/256:ℝ))
    (hy1 : (63/32:ℝ) ≤ y) (hy2 : y ≤ (1013/512:ℝ))
    (hz1 : (267/256:ℝ) ≤ z) (hz2 : z ≤ (17/16:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total z (539/512:ℝ) with hc | hc
  · rcases le_total x (1063/1024:ℝ) with hc | hc
    · rcases le_total y (2021/1024:ℝ) with hc | hc
      · rcases le_total z (1073/1024:ℝ) with hc | hc
        · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_16 x (by linarith) (by linarith)
          have hw1 : (2946158453/5000000000000:ℝ) ≤ wfun y := wc_87 y (by linarith) (by linarith)
          have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
          have hw3 : (28217469/5000000000000:ℝ) ≤ wfun (x + y) := wc_223 (x + y) (by linarith) (by linarith)
          have hw5 : (184146301/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_527 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_16 x (by linarith) (by linarith)
          have hw1 : (2946158453/5000000000000:ℝ) ≤ wfun y := wc_87 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
          have hw3 : (28217469/5000000000000:ℝ) ≤ wfun (x + y) := wc_223 (x + y) (by linarith) (by linarith)
          have hw5 : (99536523/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_537 (x + y + z) (by linarith) (by linarith)
          linarith
      · rcases le_total z (1073/1024:ℝ) with hc | hc
        · rcases le_total x (2121/2048:ℝ) with hc | hc
          · have hw0 : (1888462017/5000000000000:ℝ) ≤ wfun x := wc_15 x (by linarith) (by linarith)
            have hw1 : (4902043129/10000000000000:ℝ) ≤ wfun y := wc_96 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
            have hw3 : (3586667/1250000000000:ℝ) ≤ wfun (x + y) := wc_227 (x + y) (by linarith) (by linarith)
            have hw5 : (498883881/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_536 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total y (4047/2048:ℝ) with hc | hc
            · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
              have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_95 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
              have hw3 : (3586667/1250000000000:ℝ) ≤ wfun (x + y) := wc_229 (x + y) (by linarith) (by linarith)
              have hw5 : (572192259/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_540 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
              have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_99 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
              have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_231 (x + y) (by linarith) (by linarith)
              have hw5 : (648981217/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_543 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (2121/2048:ℝ) with hc | hc
          · have hw0 : (1888462017/5000000000000:ℝ) ≤ wfun x := wc_15 x (by linarith) (by linarith)
            have hw1 : (4902043129/10000000000000:ℝ) ≤ wfun y := wc_96 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
            have hw3 : (3586667/1250000000000:ℝ) ≤ wfun (x + y) := wc_227 (x + y) (by linarith) (by linarith)
            have hw4 : (293481/2500000000000:ℝ) ≤ wfun (y + z) := wc_244 (y + z) (by linarith) (by linarith)
            have hw5 : (323709737/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_544 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total y (4047/2048:ℝ) with hc | hc
            · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
              have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_95 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
              have hw3 : (3586667/1250000000000:ℝ) ≤ wfun (x + y) := wc_229 (x + y) (by linarith) (by linarith)
              have hw4 : (235547/2000000000000:ℝ) ≤ wfun (y + z) := wc_243 (y + z) (by linarith) (by linarith)
              have hw5 : (730420113/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_558 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
              have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_99 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
              have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_231 (x + y) (by linarith) (by linarith)
              have hw4 : (5174037/5000000000000:ℝ) ≤ wfun (y + z) := wc_257 (y + z) (by linarith) (by linarith)
              have hw5 : (25514763/312500000000:ℝ) ≤ wfun (x + y + z) := wc_561 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total y (2021/1024:ℝ) with hc | hc
      · rcases le_total z (1073/1024:ℝ) with hc | hc
        · rcases le_total x (2131/2048:ℝ) with hc | hc
          · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
            have hw1 : (2946158453/5000000000000:ℝ) ≤ wfun y := wc_87 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
            have hw3 : (3586667/1250000000000:ℝ) ≤ wfun (x + y) := wc_227 (x + y) (by linarith) (by linarith)
            have hw5 : (498883881/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_536 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total y (4037/2048:ℝ) with hc | hc
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
              have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_86 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
              have hw3 : (3586667/1250000000000:ℝ) ≤ wfun (x + y) := wc_229 (x + y) (by linarith) (by linarith)
              have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_232 (y + z) (by linarith) (by linarith)
              have hw5 : (572192259/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_540 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (2141/2048:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
                have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_92 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_231 (x + y) (by linarith) (by linarith)
                have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_234 (y + z) (by linarith) (by linarith)
                have hw5 : (162636919/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_542 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
                have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_92 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_231 (x + y) (by linarith) (by linarith)
                have hw5 : (183045519/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_557 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (2131/2048:ℝ) with hc | hc
          · rcases le_total y (4037/2048:ℝ) with hc | hc
            · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
              have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_86 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
              have hw3 : (28217469/5000000000000:ℝ) ≤ wfun (x + y) := wc_226 (x + y) (by linarith) (by linarith)
              have hw5 : (648981217/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_543 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
              have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_92 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
              have hw3 : (3586667/1250000000000:ℝ) ≤ wfun (x + y) := wc_229 (x + y) (by linarith) (by linarith)
              have hw5 : (730420113/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_558 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (4037/2048:ℝ) with hc | hc
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
              have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_86 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
              have hw3 : (3586667/1250000000000:ℝ) ≤ wfun (x + y) := wc_229 (x + y) (by linarith) (by linarith)
              have hw5 : (730420113/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_558 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (2151/2048:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
                have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_92 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_231 (x + y) (by linarith) (by linarith)
                have hw5 : (12788137/156250000000:ℝ) ≤ wfun (x + y + z) := wc_560 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
                have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_92 y (by linarith) (by linarith)
                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_231 (x + y) (by linarith) (by linarith)
                have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_242 (y + z) (by linarith) (by linarith)
                have hw5 : (56830383/625000000000:ℝ) ≤ wfun (x + y + z) := wc_571 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total z (1073/1024:ℝ) with hc | hc
        · rcases le_total x (2131/2048:ℝ) with hc | hc
          · rcases le_total y (4047/2048:ℝ) with hc | hc
            · rcases le_total z (2141/2048:ℝ) with hc | hc
              · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
                have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_95 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_231 (x + y) (by linarith) (by linarith)
                have hw5 : (162636919/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_542 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
                have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_95 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_231 (x + y) (by linarith) (by linarith)
                have hw5 : (183045519/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_557 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (2141/2048:ℝ) with hc | hc
              · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
                have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_99 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_234 (x + y) (by linarith) (by linarith)
                have hw5 : (183045519/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_557 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
                have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_99 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_234 (x + y) (by linarith) (by linarith)
                have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_242 (y + z) (by linarith) (by linarith)
                have hw5 : (12788137/156250000000:ℝ) ≤ wfun (x + y + z) := wc_560 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (4047/2048:ℝ) with hc | hc
            · rcases le_total z (2141/2048:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
                have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_95 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_234 (x + y) (by linarith) (by linarith)
                have hw5 : (183045519/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_557 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total x (4267/4096:ℝ) with hc | hc
                · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                  have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_95 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                  have hw3 : (906687/2000000000000:ℝ) ≤ wfun (x + y) := wc_233 (x + y) (by linarith) (by linarith)
                  have hw5 : (81942717/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_559 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                  have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_95 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                  have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_235 (x + y) (by linarith) (by linarith)
                  have hw5 : (864332647/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_568 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total z (2141/2048:ℝ) with hc | hc
              · rcases le_total x (4267/4096:ℝ) with hc | hc
                · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                  have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_99 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                  have hw5 : (81942717/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_559 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total y (8099/4096:ℝ) with hc | hc
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                    have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
                    have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                    have hw5 : (865374359/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_567 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                    have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                    have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                    have hw4 : (41/1250000000000:ℝ) ≤ wfun (y + z) := wc_238 (y + z) (by linarith) (by linarith)
                    have hw5 : (227869559/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_569 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total x (4267/4096:ℝ) with hc | hc
                · rcases le_total y (8099/4096:ℝ) with hc | hc
                  · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                    have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
                    have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                    have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_236 (x + y) (by linarith) (by linarith)
                    have hw4 : (29587/250000000000:ℝ) ≤ wfun (y + z) := wc_241 (y + z) (by linarith) (by linarith)
                    have hw5 : (227869559/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_569 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                    have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                    have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                    have hw4 : (465149/1000000000000:ℝ) ≤ wfun (y + z) := wc_251 (y + z) (by linarith) (by linarith)
                    have hw5 : (958721819/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_576 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total y (8099/4096:ℝ) with hc | hc
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                    have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
                    have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                    have hw4 : (29587/250000000000:ℝ) ≤ wfun (y + z) := wc_241 (y + z) (by linarith) (by linarith)
                    have hw5 : (958721819/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_576 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                    have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                    have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                    have hw4 : (465149/1000000000000:ℝ) ≤ wfun (y + z) := wc_251 (y + z) (by linarith) (by linarith)
                    have hw5 : (1007100179/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_579 (x + y + z) (by linarith) (by linarith)
                    linarith
        · rcases le_total x (2131/2048:ℝ) with hc | hc
          · rcases le_total y (4047/2048:ℝ) with hc | hc
            · rcases le_total z (2151/2048:ℝ) with hc | hc
              · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
                have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_95 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_231 (x + y) (by linarith) (by linarith)
                have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_242 (y + z) (by linarith) (by linarith)
                have hw5 : (12788137/156250000000:ℝ) ≤ wfun (x + y + z) := wc_560 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
                have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_95 y (by linarith) (by linarith)
                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_231 (x + y) (by linarith) (by linarith)
                have hw4 : (2076333/2000000000000:ℝ) ≤ wfun (y + z) := wc_256 (y + z) (by linarith) (by linarith)
                have hw5 : (56830383/625000000000:ℝ) ≤ wfun (x + y + z) := wc_571 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (2151/2048:ℝ) with hc | hc
              · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
                have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_99 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_234 (x + y) (by linarith) (by linarith)
                have hw4 : (2076333/2000000000000:ℝ) ≤ wfun (y + z) := wc_256 (y + z) (by linarith) (by linarith)
                have hw5 : (56830383/625000000000:ℝ) ≤ wfun (x + y + z) := wc_571 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
                have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_99 y (by linarith) (by linarith)
                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_234 (x + y) (by linarith) (by linarith)
                have hw4 : (14329561/5000000000000:ℝ) ≤ wfun (y + z) := wc_270 (y + z) (by linarith) (by linarith)
                have hw5 : (1004679561/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_581 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (4047/2048:ℝ) with hc | hc
            · rcases le_total z (2151/2048:ℝ) with hc | hc
              · rcases le_total x (4267/4096:ℝ) with hc | hc
                · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                  have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_95 y (by linarith) (by linarith)
                  have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                  have hw3 : (906687/2000000000000:ℝ) ≤ wfun (x + y) := wc_233 (x + y) (by linarith) (by linarith)
                  have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_242 (y + z) (by linarith) (by linarith)
                  have hw5 : (910381357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_570 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                  have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_95 y (by linarith) (by linarith)
                  have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                  have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_235 (x + y) (by linarith) (by linarith)
                  have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_242 (y + z) (by linarith) (by linarith)
                  have hw5 : (191513687/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_577 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total x (4267/4096:ℝ) with hc | hc
                · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                  have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_95 y (by linarith) (by linarith)
                  have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                  have hw3 : (906687/2000000000000:ℝ) ≤ wfun (x + y) := wc_233 (x + y) (by linarith) (by linarith)
                  have hw4 : (2076333/2000000000000:ℝ) ≤ wfun (y + z) := wc_256 (y + z) (by linarith) (by linarith)
                  have hw5 : (1005888959/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_580 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                  have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_95 y (by linarith) (by linarith)
                  have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                  have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_235 (x + y) (by linarith) (by linarith)
                  have hw4 : (2076333/2000000000000:ℝ) ≤ wfun (y + z) := wc_256 (y + z) (by linarith) (by linarith)
                  have hw5 : (1055337947/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_592 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total z (2151/2048:ℝ) with hc | hc
              · rcases le_total x (4267/4096:ℝ) with hc | hc
                · rcases le_total y (8099/4096:ℝ) with hc | hc
                  · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                    have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
                    have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                    have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_236 (x + y) (by linarith) (by linarith)
                    have hw4 : (649907/625000000000:ℝ) ≤ wfun (y + z) := wc_255 (y + z) (by linarith) (by linarith)
                    have hw5 : (1007100179/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_579 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                    have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                    have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                    have hw4 : (736743/400000000000:ℝ) ≤ wfun (y + z) := wc_263 (y + z) (by linarith) (by linarith)
                    have hw5 : (528304163/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_591 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total y (8099/4096:ℝ) with hc | hc
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                    have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
                    have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                    have hw4 : (649907/625000000000:ℝ) ≤ wfun (y + z) := wc_255 (y + z) (by linarith) (by linarith)
                    have hw5 : (528304163/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_591 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                    have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                    have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                    have hw4 : (736743/400000000000:ℝ) ≤ wfun (y + z) := wc_263 (y + z) (by linarith) (by linarith)
                    have hw5 : (553620607/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_595 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total x (4267/4096:ℝ) with hc | hc
                · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                  have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_99 y (by linarith) (by linarith)
                  have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                  have hw4 : (14329561/5000000000000:ℝ) ≤ wfun (y + z) := wc_270 (y + z) (by linarith) (by linarith)
                  have hw5 : (1105910359/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_596 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total y (8099/4096:ℝ) with hc | hc
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                    have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
                    have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                    have hw4 : (2870559/1000000000000:ℝ) ≤ wfun (y + z) := wc_269 (y + z) (by linarith) (by linarith)
                    have hw5 : (1158993733/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_603 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                    have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                    have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                    have hw4 : (20626673/5000000000000:ℝ) ≤ wfun (y + z) := wc_279 (y + z) (by linarith) (by linarith)
                    have hw5 : (242372143/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_608 (x + y + z) (by linarith) (by linarith)
                    linarith
  · rcases le_total x (1063/1024:ℝ) with hc | hc
    · rcases le_total y (2021/1024:ℝ) with hc | hc
      · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_16 x (by linarith) (by linarith)
        have hw1 : (2946158453/5000000000000:ℝ) ≤ wfun y := wc_87 y (by linarith) (by linarith)
        have hw3 : (28217469/5000000000000:ℝ) ≤ wfun (x + y) := wc_223 (x + y) (by linarith) (by linarith)
        have hw4 : (1166349/10000000000000:ℝ) ≤ wfun (y + z) := wc_245 (y + z) (by linarith) (by linarith)
        have hw5 : (160690591/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_546 (x + y + z) (by linarith) (by linarith)
        linarith
      · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_16 x (by linarith) (by linarith)
        have hw1 : (4902043129/10000000000000:ℝ) ≤ wfun y := wc_96 y (by linarith) (by linarith)
        have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_228 (x + y) (by linarith) (by linarith)
        have hw4 : (28290747/10000000000000:ℝ) ≤ wfun (y + z) := wc_273 (y + z) (by linarith) (by linarith)
        have hw5 : (808657969/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_564 (x + y + z) (by linarith) (by linarith)
        linarith
    · rcases le_total y (2021/1024:ℝ) with hc | hc
      · rcases le_total z (1083/1024:ℝ) with hc | hc
        · rcases le_total x (2131/2048:ℝ) with hc | hc
          · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
            have hw1 : (2946158453/5000000000000:ℝ) ≤ wfun y := wc_87 y (by linarith) (by linarith)
            have hw3 : (3586667/1250000000000:ℝ) ≤ wfun (x + y) := wc_227 (x + y) (by linarith) (by linarith)
            have hw4 : (293481/2500000000000:ℝ) ≤ wfun (y + z) := wc_244 (y + z) (by linarith) (by linarith)
            have hw5 : (407254991/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_562 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total y (4037/2048:ℝ) with hc | hc
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
              have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_86 y (by linarith) (by linarith)
              have hw3 : (3586667/1250000000000:ℝ) ≤ wfun (x + y) := wc_229 (x + y) (by linarith) (by linarith)
              have hw4 : (235547/2000000000000:ℝ) ≤ wfun (y + z) := wc_243 (y + z) (by linarith) (by linarith)
              have hw5 : (907100611/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_572 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
              have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_92 y (by linarith) (by linarith)
              have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_231 (x + y) (by linarith) (by linarith)
              have hw4 : (5174037/5000000000000:ℝ) ≤ wfun (y + z) := wc_257 (y + z) (by linarith) (by linarith)
              have hw5 : (200453243/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_582 (x + y + z) (by linarith) (by linarith)
              linarith
        · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
          have hw1 : (2946158453/5000000000000:ℝ) ≤ wfun y := wc_87 y (by linarith) (by linarith)
          have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
          have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_228 (x + y) (by linarith) (by linarith)
          have hw4 : (28474189/10000000000000:ℝ) ≤ wfun (y + z) := wc_272 (y + z) (by linarith) (by linarith)
          have hw5 : (249365309/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_584 (x + y + z) (by linarith) (by linarith)
          linarith
      · rcases le_total z (1083/1024:ℝ) with hc | hc
        · rcases le_total x (2131/2048:ℝ) with hc | hc
          · rcases le_total y (4047/2048:ℝ) with hc | hc
            · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
              have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_95 y (by linarith) (by linarith)
              have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_231 (x + y) (by linarith) (by linarith)
              have hw4 : (7141617/2500000000000:ℝ) ≤ wfun (y + z) := wc_271 (y + z) (by linarith) (by linarith)
              have hw5 : (200453243/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_582 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
              have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_99 y (by linarith) (by linarith)
              have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_234 (x + y) (by linarith) (by linarith)
              have hw4 : (27892031/5000000000000:ℝ) ≤ wfun (y + z) := wc_287 (y + z) (by linarith) (by linarith)
              have hw5 : (55096489/500000000000:ℝ) ≤ wfun (x + y + z) := wc_598 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (4047/2048:ℝ) with hc | hc
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
              have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_95 y (by linarith) (by linarith)
              have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_234 (x + y) (by linarith) (by linarith)
              have hw4 : (7141617/2500000000000:ℝ) ≤ wfun (y + z) := wc_271 (y + z) (by linarith) (by linarith)
              have hw5 : (55096489/500000000000:ℝ) ≤ wfun (x + y + z) := wc_598 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
              have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_99 y (by linarith) (by linarith)
              have hw4 : (27892031/5000000000000:ℝ) ≤ wfun (y + z) := wc_287 (y + z) (by linarith) (by linarith)
              have hw5 : (1206050917/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_611 (x + y + z) (by linarith) (by linarith)
              linarith
        · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
          have hw1 : (4902043129/10000000000000:ℝ) ≤ wfun y := wc_96 y (by linarith) (by linarith)
          have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
          have hw4 : (11456693/1250000000000:ℝ) ≤ wfun (y + z) := wc_302 (y + z) (by linarith) (by linarith)
          have hw5 : (600137957/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_613 (x + y + z) (by linarith) (by linarith)
          linarith

set_option maxHeartbeats 20000000 in
lemma ch_16 (x y z : ℝ) (hx1 : (529/512:ℝ) ≤ x) (hx2 : x ≤ (267/256:ℝ))
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
    · rcases le_total x (1063/1024:ℝ) with hc | hc
      · rcases le_total y (2041/1024:ℝ) with hc | hc
        · rcases le_total z (1073/1024:ℝ) with hc | hc
          · rcases le_total x (2121/2048:ℝ) with hc | hc
            · rcases le_total y (4077/2048:ℝ) with hc | hc
              · have hw0 : (1888462017/5000000000000:ℝ) ≤ wfun x := wc_15 x (by linarith) (by linarith)
                have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_127 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
                have hw3 : (1181561/10000000000000:ℝ) ≤ wfun (x + y) := wc_242 (x + y) (by linarith) (by linarith)
                have hw4 : (22987523/2500000000000:ℝ) ≤ wfun (y + z) := wc_301 (y + z) (by linarith) (by linarith)
                have hw5 : (200453243/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_582 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1888462017/5000000000000:ℝ) ≤ wfun x := wc_15 x (by linarith) (by linarith)
                have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_133 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
                have hw3 : (2076333/2000000000000:ℝ) ≤ wfun (x + y) := wc_256 (x + y) (by linarith) (by linarith)
                have hw4 : (2140811/156250000000:ℝ) ≤ wfun (y + z) := wc_321 (y + z) (by linarith) (by linarith)
                have hw5 : (55096489/500000000000:ℝ) ≤ wfun (x + y + z) := wc_598 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (4077/2048:ℝ) with hc | hc
              · rcases le_total z (2141/2048:ℝ) with hc | hc
                · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
                  have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_127 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                  have hw3 : (2076333/2000000000000:ℝ) ≤ wfun (x + y) := wc_256 (x + y) (by linarith) (by linarith)
                  have hw4 : (92247841/10000000000000:ℝ) ≤ wfun (y + z) := wc_300 (y + z) (by linarith) (by linarith)
                  have hw5 : (8629543/78125000000:ℝ) ≤ wfun (x + y + z) := wc_597 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
                  have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_127 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                  have hw3 : (2076333/2000000000000:ℝ) ≤ wfun (x + y) := wc_256 (x + y) (by linarith) (by linarith)
                  have hw4 : (13745521/1000000000000:ℝ) ≤ wfun (y + z) := wc_320 (y + z) (by linarith) (by linarith)
                  have hw5 : (1208951451/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_610 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (2141/2048:ℝ) with hc | hc
                · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
                  have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_133 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                  have hw3 : (14329561/5000000000000:ℝ) ≤ wfun (x + y) := wc_270 (x + y) (by linarith) (by linarith)
                  have hw4 : (13745521/1000000000000:ℝ) ≤ wfun (y + z) := wc_320 (y + z) (by linarith) (by linarith)
                  have hw5 : (1208951451/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_610 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
                  have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_133 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                  have hw3 : (14329561/5000000000000:ℝ) ≤ wfun (x + y) := wc_270 (x + y) (by linarith) (by linarith)
                  have hw4 : (23941523/1250000000000:ℝ) ≤ wfun (y + z) := wc_326 (y + z) (by linarith) (by linarith)
                  have hw5 : (263549591/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_631 (x + y + z) (by linarith) (by linarith)
                  linarith
          · rcases le_total x (2121/2048:ℝ) with hc | hc
            · have hw0 : (1888462017/5000000000000:ℝ) ≤ wfun x := wc_15 x (by linarith) (by linarith)
              have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
              have hw3 : (235547/2000000000000:ℝ) ≤ wfun (x + y) := wc_243 (x + y) (by linarith) (by linarith)
              have hw4 : (190300253/10000000000000:ℝ) ≤ wfun (y + z) := wc_328 (y + z) (by linarith) (by linarith)
              have hw5 : (1203159081/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_612 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total y (4077/2048:ℝ) with hc | hc
              · rcases le_total z (2151/2048:ℝ) with hc | hc
                · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
                  have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_127 y (by linarith) (by linarith)
                  have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                  have hw3 : (2076333/2000000000000:ℝ) ≤ wfun (x + y) := wc_256 (x + y) (by linarith) (by linarith)
                  have hw4 : (23941523/1250000000000:ℝ) ≤ wfun (y + z) := wc_326 (y + z) (by linarith) (by linarith)
                  have hw5 : (263549591/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_631 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
                  have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_127 y (by linarith) (by linarith)
                  have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                  have hw3 : (2076333/2000000000000:ℝ) ≤ wfun (x + y) := wc_256 (x + y) (by linarith) (by linarith)
                  have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_334 (y + z) (by linarith) (by linarith)
                  have hw5 : (715464319/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_648 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
                have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_133 y (by linarith) (by linarith)
                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
                have hw3 : (14329561/5000000000000:ℝ) ≤ wfun (x + y) := wc_270 (x + y) (by linarith) (by linarith)
                have hw4 : (63400731/2500000000000:ℝ) ≤ wfun (y + z) := wc_335 (y + z) (by linarith) (by linarith)
                have hw5 : (1427499659/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_649 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (1073/1024:ℝ) with hc | hc
          · rcases le_total x (2121/2048:ℝ) with hc | hc
            · have hw0 : (1888462017/5000000000000:ℝ) ≤ wfun x := wc_15 x (by linarith) (by linarith)
              have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
              have hw3 : (7141617/2500000000000:ℝ) ≤ wfun (x + y) := wc_271 (x + y) (by linarith) (by linarith)
              have hw4 : (190300253/10000000000000:ℝ) ≤ wfun (y + z) := wc_328 (y + z) (by linarith) (by linarith)
              have hw5 : (1203159081/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_612 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total y (4087/2048:ℝ) with hc | hc
              · rcases le_total z (2141/2048:ℝ) with hc | hc
                · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
                  have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_135 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                  have hw3 : (55964847/10000000000000:ℝ) ≤ wfun (x + y) := wc_286 (x + y) (by linarith) (by linarith)
                  have hw4 : (23941523/1250000000000:ℝ) ≤ wfun (y + z) := wc_326 (y + z) (by linarith) (by linarith)
                  have hw5 : (263549591/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_631 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
                  have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_135 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                  have hw3 : (55964847/10000000000000:ℝ) ≤ wfun (x + y) := wc_286 (x + y) (by linarith) (by linarith)
                  have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_334 (y + z) (by linarith) (by linarith)
                  have hw5 : (715464319/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_648 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
                have hw1 : (1868712167/10000000000000:ℝ) ≤ wfun y := wc_137 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
                have hw3 : (92247841/10000000000000:ℝ) ≤ wfun (x + y) := wc_300 (x + y) (by linarith) (by linarith)
                have hw4 : (63400731/2500000000000:ℝ) ≤ wfun (y + z) := wc_335 (y + z) (by linarith) (by linarith)
                have hw5 : (1427499659/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_649 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (2121/2048:ℝ) with hc | hc
            · have hw0 : (1888462017/5000000000000:ℝ) ≤ wfun x := wc_15 x (by linarith) (by linarith)
              have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
              have hw3 : (7141617/2500000000000:ℝ) ≤ wfun (x + y) := wc_271 (x + y) (by linarith) (by linarith)
              have hw4 : (161986357/5000000000000:ℝ) ≤ wfun (y + z) := wc_342 (y + z) (by linarith) (by linarith)
              have hw5 : (1424080951/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_650 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total y (4087/2048:ℝ) with hc | hc
              · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
                have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_135 y (by linarith) (by linarith)
                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
                have hw3 : (55964847/10000000000000:ℝ) ≤ wfun (x + y) := wc_286 (x + y) (by linarith) (by linarith)
                have hw4 : (325017537/10000000000000:ℝ) ≤ wfun (y + z) := wc_341 (y + z) (by linarith) (by linarith)
                have hw5 : (1544741841/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_675 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
                have hw1 : (1868712167/10000000000000:ℝ) ≤ wfun y := wc_137 y (by linarith) (by linarith)
                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
                have hw3 : (92247841/10000000000000:ℝ) ≤ wfun (x + y) := wc_300 (x + y) (by linarith) (by linarith)
                have hw4 : (405098789/10000000000000:ℝ) ≤ wfun (y + z) := wc_347 (y + z) (by linarith) (by linarith)
                have hw5 : (1666270777/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_689 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total y (2041/1024:ℝ) with hc | hc
        · rcases le_total z (1073/1024:ℝ) with hc | hc
          · rcases le_total x (2131/2048:ℝ) with hc | hc
            · rcases le_total y (4077/2048:ℝ) with hc | hc
              · rcases le_total z (2141/2048:ℝ) with hc | hc
                · rcases le_total x (4257/4096:ℝ) with hc | hc
                  · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
                    have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_127 y (by linarith) (by linarith)
                    have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                    have hw3 : (2870559/1000000000000:ℝ) ≤ wfun (x + y) := wc_269 (x + y) (by linarith) (by linarith)
                    have hw4 : (92247841/10000000000000:ℝ) ≤ wfun (y + z) := wc_300 (y + z) (by linarith) (by linarith)
                    have hw5 : (121040499/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_609 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · rcases le_total y (8149/4096:ℝ) with hc | hc
                    · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_22 x (by linarith) (by linarith)
                      have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_126 y (by linarith) (by linarith)
                      have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                      have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_278 (x + y) (by linarith) (by linarith)
                      have hw4 : (5774823/625000000000:ℝ) ≤ wfun (y + z) := wc_299 (y + z) (by linarith) (by linarith)
                      have hw5 : (1265836939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_621 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_22 x (by linarith) (by linarith)
                      have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
                      have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                      have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_284 (x + y) (by linarith) (by linarith)
                      have hw4 : (569617/50000000000:ℝ) ≤ wfun (y + z) := wc_316 (y + z) (by linarith) (by linarith)
                      have hw5 : (660458559/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_629 (x + y + z) (by linarith) (by linarith)
                      linarith
                · rcases le_total x (4257/4096:ℝ) with hc | hc
                  · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
                    have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_127 y (by linarith) (by linarith)
                    have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                    have hw3 : (2870559/1000000000000:ℝ) ≤ wfun (x + y) := wc_269 (x + y) (by linarith) (by linarith)
                    have hw4 : (13745521/1000000000000:ℝ) ≤ wfun (y + z) := wc_320 (y + z) (by linarith) (by linarith)
                    have hw5 : (659665673/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_630 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · rcases le_total y (8149/4096:ℝ) with hc | hc
                    · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_22 x (by linarith) (by linarith)
                      have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_126 y (by linarith) (by linarith)
                      have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                      have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_278 (x + y) (by linarith) (by linarith)
                      have hw4 : (4302423/312500000000:ℝ) ≤ wfun (y + z) := wc_319 (y + z) (by linarith) (by linarith)
                      have hw5 : (172136989/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_639 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_22 x (by linarith) (by linarith)
                      have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
                      have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                      have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_284 (x + y) (by linarith) (by linarith)
                      have hw4 : (163652657/10000000000000:ℝ) ≤ wfun (y + z) := wc_323 (y + z) (by linarith) (by linarith)
                      have hw5 : (57374717/400000000000:ℝ) ≤ wfun (x + y + z) := wc_646 (x + y + z) (by linarith) (by linarith)
                      linarith
              · rcases le_total z (2141/2048:ℝ) with hc | hc
                · rcases le_total x (4257/4096:ℝ) with hc | hc
                  · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
                    have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_133 y (by linarith) (by linarith)
                    have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                    have hw3 : (28027757/5000000000000:ℝ) ≤ wfun (x + y) := wc_285 (x + y) (by linarith) (by linarith)
                    have hw4 : (13745521/1000000000000:ℝ) ≤ wfun (y + z) := wc_320 (y + z) (by linarith) (by linarith)
                    have hw5 : (659665673/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_630 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_22 x (by linarith) (by linarith)
                    have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_133 y (by linarith) (by linarith)
                    have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                    have hw3 : (18276411/2500000000000:ℝ) ≤ wfun (x + y) := wc_293 (x + y) (by linarith) (by linarith)
                    have hw4 : (13745521/1000000000000:ℝ) ≤ wfun (y + z) := wc_320 (y + z) (by linarith) (by linarith)
                    have hw5 : (275088639/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_640 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total x (4257/4096:ℝ) with hc | hc
                  · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
                    have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_133 y (by linarith) (by linarith)
                    have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                    have hw3 : (28027757/5000000000000:ℝ) ≤ wfun (x + y) := wc_285 (x + y) (by linarith) (by linarith)
                    have hw4 : (23941523/1250000000000:ℝ) ≤ wfun (y + z) := wc_326 (y + z) (by linarith) (by linarith)
                    have hw5 : (1432646991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_647 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_22 x (by linarith) (by linarith)
                    have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_133 y (by linarith) (by linarith)
                    have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                    have hw3 : (18276411/2500000000000:ℝ) ≤ wfun (x + y) := wc_293 (x + y) (by linarith) (by linarith)
                    have hw4 : (23941523/1250000000000:ℝ) ≤ wfun (y + z) := wc_326 (y + z) (by linarith) (by linarith)
                    have hw5 : (298187457/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_666 (x + y + z) (by linarith) (by linarith)
                    linarith
            · rcases le_total y (4077/2048:ℝ) with hc | hc
              · rcases le_total z (2141/2048:ℝ) with hc | hc
                · rcases le_total x (4267/4096:ℝ) with hc | hc
                  · rcases le_total y (8149/4096:ℝ) with hc | hc
                    · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                      have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_126 y (by linarith) (by linarith)
                      have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                      have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_284 (x + y) (by linarith) (by linarith)
                      have hw4 : (5774823/625000000000:ℝ) ≤ wfun (y + z) := wc_299 (y + z) (by linarith) (by linarith)
                      have hw5 : (660458559/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_629 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                      have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
                      have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                      have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_292 (x + y) (by linarith) (by linarith)
                      have hw4 : (569617/50000000000:ℝ) ≤ wfun (y + z) := wc_316 (y + z) (by linarith) (by linarith)
                      have hw5 : (172136989/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_639 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · rcases le_total y (8149/4096:ℝ) with hc | hc
                    · rcases le_total z (4277/4096:ℝ) with hc | hc
                      · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                        have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_126 y (by linarith) (by linarith)
                        have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
                        have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_292 (x + y) (by linarith) (by linarith)
                        have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
                        have hw5 : (275750223/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_638 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                        have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_126 y (by linarith) (by linarith)
                        have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                        have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_292 (x + y) (by linarith) (by linarith)
                        have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_315 (y + z) (by linarith) (by linarith)
                        have hw5 : (718045723/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_645 (x + y + z) (by linarith) (by linarith)
                        linarith
                    · rcases le_total z (4277/4096:ℝ) with hc | hc
                      · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                        have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
                        have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
                        have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_298 (x + y) (by linarith) (by linarith)
                        have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_315 (y + z) (by linarith) (by linarith)
                        have hw5 : (718045723/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_645 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                        have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
                        have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                        have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_298 (x + y) (by linarith) (by linarith)
                        have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_318 (y + z) (by linarith) (by linarith)
                        have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_664 (x + y + z) (by linarith) (by linarith)
                        linarith
                · rcases le_total x (4267/4096:ℝ) with hc | hc
                  · rcases le_total y (8149/4096:ℝ) with hc | hc
                    · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                      have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_126 y (by linarith) (by linarith)
                      have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                      have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_284 (x + y) (by linarith) (by linarith)
                      have hw4 : (4302423/312500000000:ℝ) ≤ wfun (y + z) := wc_319 (y + z) (by linarith) (by linarith)
                      have hw5 : (57374717/400000000000:ℝ) ≤ wfun (x + y + z) := wc_646 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                      have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
                      have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                      have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_292 (x + y) (by linarith) (by linarith)
                      have hw4 : (163652657/10000000000000:ℝ) ≤ wfun (y + z) := wc_323 (y + z) (by linarith) (by linarith)
                      have hw5 : (1492727701/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_665 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · rcases le_total y (8149/4096:ℝ) with hc | hc
                    · rcases le_total z (4287/4096:ℝ) with hc | hc
                      · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                        have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_126 y (by linarith) (by linarith)
                        have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                        have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_292 (x + y) (by linarith) (by linarith)
                        have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_318 (y + z) (by linarith) (by linarith)
                        have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_664 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                        have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_126 y (by linarith) (by linarith)
                        have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                        have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_292 (x + y) (by linarith) (by linarith)
                        have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_322 (y + z) (by linarith) (by linarith)
                        have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_671 (x + y + z) (by linarith) (by linarith)
                        linarith
                    · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                      have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
                      have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                      have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_298 (x + y) (by linarith) (by linarith)
                      have hw4 : (163652657/10000000000000:ℝ) ≤ wfun (y + z) := wc_323 (y + z) (by linarith) (by linarith)
                      have hw5 : (62086789/400000000000:ℝ) ≤ wfun (x + y + z) := wc_672 (x + y + z) (by linarith) (by linarith)
                      linarith
              · rcases le_total z (2141/2048:ℝ) with hc | hc
                · rcases le_total x (4267/4096:ℝ) with hc | hc
                  · rcases le_total y (8159/4096:ℝ) with hc | hc
                    · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                      have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_132 y (by linarith) (by linarith)
                      have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                      have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_298 (x + y) (by linarith) (by linarith)
                      have hw4 : (4302423/312500000000:ℝ) ≤ wfun (y + z) := wc_319 (y + z) (by linarith) (by linarith)
                      have hw5 : (57374717/400000000000:ℝ) ≤ wfun (x + y + z) := wc_646 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                      have hw1 : (1245909663/5000000000000:ℝ) ≤ wfun y := wc_134 y (by linarith) (by linarith)
                      have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                      have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_315 (x + y) (by linarith) (by linarith)
                      have hw4 : (163652657/10000000000000:ℝ) ≤ wfun (y + z) := wc_323 (y + z) (by linarith) (by linarith)
                      have hw5 : (1492727701/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_665 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · rcases le_total y (8159/4096:ℝ) with hc | hc
                    · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                      have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_132 y (by linarith) (by linarith)
                      have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                      have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_315 (x + y) (by linarith) (by linarith)
                      have hw4 : (4302423/312500000000:ℝ) ≤ wfun (y + z) := wc_319 (y + z) (by linarith) (by linarith)
                      have hw5 : (1492727701/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_665 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                      have hw1 : (1245909663/5000000000000:ℝ) ≤ wfun y := wc_134 y (by linarith) (by linarith)
                      have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                      have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_318 (x + y) (by linarith) (by linarith)
                      have hw4 : (163652657/10000000000000:ℝ) ≤ wfun (y + z) := wc_323 (y + z) (by linarith) (by linarith)
                      have hw5 : (62086789/400000000000:ℝ) ≤ wfun (x + y + z) := wc_672 (x + y + z) (by linarith) (by linarith)
                      linarith
                · rcases le_total x (4267/4096:ℝ) with hc | hc
                  · rcases le_total y (8159/4096:ℝ) with hc | hc
                    · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                      have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_132 y (by linarith) (by linarith)
                      have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                      have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_298 (x + y) (by linarith) (by linarith)
                      have hw4 : (47960431/2500000000000:ℝ) ≤ wfun (y + z) := wc_325 (y + z) (by linarith) (by linarith)
                      have hw5 : (62086789/400000000000:ℝ) ≤ wfun (x + y + z) := wc_672 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                      have hw1 : (1245909663/5000000000000:ℝ) ≤ wfun y := wc_134 y (by linarith) (by linarith)
                      have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                      have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_315 (x + y) (by linarith) (by linarith)
                      have hw4 : (111118793/5000000000000:ℝ) ≤ wfun (y + z) := wc_331 (y + z) (by linarith) (by linarith)
                      have hw5 : (322537687/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_681 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · rcases le_total y (8159/4096:ℝ) with hc | hc
                    · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                      have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_132 y (by linarith) (by linarith)
                      have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                      have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_315 (x + y) (by linarith) (by linarith)
                      have hw4 : (47960431/2500000000000:ℝ) ≤ wfun (y + z) := wc_325 (y + z) (by linarith) (by linarith)
                      have hw5 : (322537687/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_681 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                      have hw1 : (1245909663/5000000000000:ℝ) ≤ wfun y := wc_134 y (by linarith) (by linarith)
                      have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                      have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_318 (x + y) (by linarith) (by linarith)
                      have hw4 : (111118793/5000000000000:ℝ) ≤ wfun (y + z) := wc_331 (y + z) (by linarith) (by linarith)
                      have hw5 : (334855641/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_686 (x + y + z) (by linarith) (by linarith)
                      linarith
          · rcases le_total x (2131/2048:ℝ) with hc | hc
            · rcases le_total y (4077/2048:ℝ) with hc | hc
              · rcases le_total z (2151/2048:ℝ) with hc | hc
                · rcases le_total x (4257/4096:ℝ) with hc | hc
                  · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
                    have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_127 y (by linarith) (by linarith)
                    have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                    have hw3 : (2870559/1000000000000:ℝ) ≤ wfun (x + y) := wc_269 (x + y) (by linarith) (by linarith)
                    have hw4 : (23941523/1250000000000:ℝ) ≤ wfun (y + z) := wc_326 (y + z) (by linarith) (by linarith)
                    have hw5 : (1432646991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_647 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_22 x (by linarith) (by linarith)
                    have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_127 y (by linarith) (by linarith)
                    have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                    have hw3 : (20626673/5000000000000:ℝ) ≤ wfun (x + y) := wc_279 (x + y) (by linarith) (by linarith)
                    have hw4 : (23941523/1250000000000:ℝ) ≤ wfun (y + z) := wc_326 (y + z) (by linarith) (by linarith)
                    have hw5 : (298187457/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_666 (x + y + z) (by linarith) (by linarith)
                    linarith
                · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
                  have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_127 y (by linarith) (by linarith)
                  have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                  have hw3 : (14329561/5000000000000:ℝ) ≤ wfun (x + y) := wc_270 (x + y) (by linarith) (by linarith)
                  have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_334 (y + z) (by linarith) (by linarith)
                  have hw5 : (1548450213/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_674 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (2151/2048:ℝ) with hc | hc
                · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
                  have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_133 y (by linarith) (by linarith)
                  have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                  have hw3 : (55964847/10000000000000:ℝ) ≤ wfun (x + y) := wc_286 (x + y) (by linarith) (by linarith)
                  have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_334 (y + z) (by linarith) (by linarith)
                  have hw5 : (1548450213/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_674 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
                  have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_133 y (by linarith) (by linarith)
                  have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                  have hw3 : (55964847/10000000000000:ℝ) ≤ wfun (x + y) := wc_286 (x + y) (by linarith) (by linarith)
                  have hw4 : (326066581/10000000000000:ℝ) ≤ wfun (y + z) := wc_340 (y + z) (by linarith) (by linarith)
                  have hw5 : (1670268489/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_688 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total y (4077/2048:ℝ) with hc | hc
              · rcases le_total z (2151/2048:ℝ) with hc | hc
                · rcases le_total x (4267/4096:ℝ) with hc | hc
                  · rcases le_total y (8149/4096:ℝ) with hc | hc
                    · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                      have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_126 y (by linarith) (by linarith)
                      have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                      have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_284 (x + y) (by linarith) (by linarith)
                      have hw4 : (47960431/2500000000000:ℝ) ≤ wfun (y + z) := wc_325 (y + z) (by linarith) (by linarith)
                      have hw5 : (62086789/400000000000:ℝ) ≤ wfun (x + y + z) := wc_672 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                      have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
                      have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                      have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_292 (x + y) (by linarith) (by linarith)
                      have hw4 : (111118793/5000000000000:ℝ) ≤ wfun (y + z) := wc_331 (y + z) (by linarith) (by linarith)
                      have hw5 : (322537687/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_681 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · rcases le_total y (8149/4096:ℝ) with hc | hc
                    · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                      have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_126 y (by linarith) (by linarith)
                      have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                      have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_292 (x + y) (by linarith) (by linarith)
                      have hw4 : (47960431/2500000000000:ℝ) ≤ wfun (y + z) := wc_325 (y + z) (by linarith) (by linarith)
                      have hw5 : (322537687/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_681 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                      have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
                      have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                      have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_298 (x + y) (by linarith) (by linarith)
                      have hw4 : (111118793/5000000000000:ℝ) ≤ wfun (y + z) := wc_331 (y + z) (by linarith) (by linarith)
                      have hw5 : (334855641/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_686 (x + y + z) (by linarith) (by linarith)
                      linarith
                · rcases le_total x (4267/4096:ℝ) with hc | hc
                  · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                    have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_127 y (by linarith) (by linarith)
                    have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                    have hw3 : (28027757/5000000000000:ℝ) ≤ wfun (x + y) := wc_285 (x + y) (by linarith) (by linarith)
                    have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_334 (y + z) (by linarith) (by linarith)
                    have hw5 : (418067961/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_687 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                    have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_127 y (by linarith) (by linarith)
                    have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                    have hw3 : (18276411/2500000000000:ℝ) ≤ wfun (x + y) := wc_293 (x + y) (by linarith) (by linarith)
                    have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_334 (y + z) (by linarith) (by linarith)
                    have hw5 : (867426269/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_698 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total z (2151/2048:ℝ) with hc | hc
                · rcases le_total x (4267/4096:ℝ) with hc | hc
                  · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                    have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_133 y (by linarith) (by linarith)
                    have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                    have hw3 : (5774823/625000000000:ℝ) ≤ wfun (x + y) := wc_299 (x + y) (by linarith) (by linarith)
                    have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_334 (y + z) (by linarith) (by linarith)
                    have hw5 : (418067961/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_687 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                    have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_133 y (by linarith) (by linarith)
                    have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                    have hw3 : (569617/50000000000:ℝ) ≤ wfun (x + y) := wc_316 (x + y) (by linarith) (by linarith)
                    have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_334 (y + z) (by linarith) (by linarith)
                    have hw5 : (867426269/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_698 (x + y + z) (by linarith) (by linarith)
                    linarith
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
                  have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_133 y (by linarith) (by linarith)
                  have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                  have hw3 : (92247841/10000000000000:ℝ) ≤ wfun (x + y) := wc_300 (x + y) (by linarith) (by linarith)
                  have hw4 : (326066581/10000000000000:ℝ) ≤ wfun (y + z) := wc_340 (y + z) (by linarith) (by linarith)
                  have hw5 : (1796338383/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_702 (x + y + z) (by linarith) (by linarith)
                  linarith
        · rcases le_total z (1073/1024:ℝ) with hc | hc
          · rcases le_total x (2131/2048:ℝ) with hc | hc
            · rcases le_total y (4087/2048:ℝ) with hc | hc
              · rcases le_total z (2141/2048:ℝ) with hc | hc
                · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
                  have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_135 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                  have hw3 : (92247841/10000000000000:ℝ) ≤ wfun (x + y) := wc_300 (x + y) (by linarith) (by linarith)
                  have hw4 : (23941523/1250000000000:ℝ) ≤ wfun (y + z) := wc_326 (y + z) (by linarith) (by linarith)
                  have hw5 : (715464319/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_648 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
                  have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_135 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                  have hw3 : (92247841/10000000000000:ℝ) ≤ wfun (x + y) := wc_300 (x + y) (by linarith) (by linarith)
                  have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_334 (y + z) (by linarith) (by linarith)
                  have hw5 : (1548450213/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_674 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (2141/2048:ℝ) with hc | hc
                · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
                  have hw1 : (1868712167/10000000000000:ℝ) ≤ wfun y := wc_137 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                  have hw3 : (13745521/1000000000000:ℝ) ≤ wfun (x + y) := wc_320 (x + y) (by linarith) (by linarith)
                  have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_334 (y + z) (by linarith) (by linarith)
                  have hw5 : (1548450213/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_674 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
                  have hw1 : (1868712167/10000000000000:ℝ) ≤ wfun y := wc_137 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                  have hw3 : (13745521/1000000000000:ℝ) ≤ wfun (x + y) := wc_320 (x + y) (by linarith) (by linarith)
                  have hw4 : (326066581/10000000000000:ℝ) ≤ wfun (y + z) := wc_340 (y + z) (by linarith) (by linarith)
                  have hw5 : (1670268489/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_688 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total y (4087/2048:ℝ) with hc | hc
              · rcases le_total z (2141/2048:ℝ) with hc | hc
                · rcases le_total x (4267/4096:ℝ) with hc | hc
                  · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                    have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_135 y (by linarith) (by linarith)
                    have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                    have hw3 : (4302423/312500000000:ℝ) ≤ wfun (x + y) := wc_319 (x + y) (by linarith) (by linarith)
                    have hw4 : (23941523/1250000000000:ℝ) ≤ wfun (y + z) := wc_326 (y + z) (by linarith) (by linarith)
                    have hw5 : (775154287/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_673 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                    have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_135 y (by linarith) (by linarith)
                    have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                    have hw3 : (163652657/10000000000000:ℝ) ≤ wfun (x + y) := wc_323 (x + y) (by linarith) (by linarith)
                    have hw4 : (23941523/1250000000000:ℝ) ≤ wfun (y + z) := wc_326 (y + z) (by linarith) (by linarith)
                    have hw5 : (1610755299/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_682 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total x (4267/4096:ℝ) with hc | hc
                  · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                    have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_135 y (by linarith) (by linarith)
                    have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                    have hw3 : (4302423/312500000000:ℝ) ≤ wfun (x + y) := wc_319 (x + y) (by linarith) (by linarith)
                    have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_334 (y + z) (by linarith) (by linarith)
                    have hw5 : (418067961/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_687 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                    have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_135 y (by linarith) (by linarith)
                    have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                    have hw3 : (163652657/10000000000000:ℝ) ≤ wfun (x + y) := wc_323 (x + y) (by linarith) (by linarith)
                    have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_334 (y + z) (by linarith) (by linarith)
                    have hw5 : (867426269/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_698 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total z (2141/2048:ℝ) with hc | hc
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
                  have hw1 : (1868712167/10000000000000:ℝ) ≤ wfun y := wc_137 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                  have hw3 : (23941523/1250000000000:ℝ) ≤ wfun (x + y) := wc_326 (x + y) (by linarith) (by linarith)
                  have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_334 (y + z) (by linarith) (by linarith)
                  have hw5 : (1670268489/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_688 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
                  have hw1 : (1868712167/10000000000000:ℝ) ≤ wfun y := wc_137 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                  have hw3 : (23941523/1250000000000:ℝ) ≤ wfun (x + y) := wc_326 (x + y) (by linarith) (by linarith)
                  have hw4 : (326066581/10000000000000:ℝ) ≤ wfun (y + z) := wc_340 (y + z) (by linarith) (by linarith)
                  have hw5 : (1796338383/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_702 (x + y + z) (by linarith) (by linarith)
                  linarith
          · rcases le_total x (2131/2048:ℝ) with hc | hc
            · rcases le_total y (4087/2048:ℝ) with hc | hc
              · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
                have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_135 y (by linarith) (by linarith)
                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
                have hw3 : (92247841/10000000000000:ℝ) ≤ wfun (x + y) := wc_300 (x + y) (by linarith) (by linarith)
                have hw4 : (325017537/10000000000000:ℝ) ≤ wfun (y + z) := wc_341 (y + z) (by linarith) (by linarith)
                have hw5 : (1666270777/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_689 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
                have hw1 : (1868712167/10000000000000:ℝ) ≤ wfun y := wc_137 y (by linarith) (by linarith)
                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
                have hw3 : (13745521/1000000000000:ℝ) ≤ wfun (x + y) := wc_320 (x + y) (by linarith) (by linarith)
                have hw4 : (405098789/10000000000000:ℝ) ≤ wfun (y + z) := wc_347 (y + z) (by linarith) (by linarith)
                have hw5 : (1792041507/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_703 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (4087/2048:ℝ) with hc | hc
              · rcases le_total z (2151/2048:ℝ) with hc | hc
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
                  have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_135 y (by linarith) (by linarith)
                  have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                  have hw3 : (13745521/1000000000000:ℝ) ≤ wfun (x + y) := wc_320 (x + y) (by linarith) (by linarith)
                  have hw4 : (326066581/10000000000000:ℝ) ≤ wfun (y + z) := wc_340 (y + z) (by linarith) (by linarith)
                  have hw5 : (1796338383/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_702 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
                  have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_135 y (by linarith) (by linarith)
                  have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                  have hw3 : (13745521/1000000000000:ℝ) ≤ wfun (x + y) := wc_320 (x + y) (by linarith) (by linarith)
                  have hw4 : (406405247/10000000000000:ℝ) ≤ wfun (y + z) := wc_346 (y + z) (by linarith) (by linarith)
                  have hw5 : (963306969/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_710 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
                have hw1 : (1868712167/10000000000000:ℝ) ≤ wfun y := wc_137 y (by linarith) (by linarith)
                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
                have hw3 : (23941523/1250000000000:ℝ) ≤ wfun (x + y) := wc_326 (x + y) (by linarith) (by linarith)
                have hw4 : (405098789/10000000000000:ℝ) ≤ wfun (y + z) := wc_347 (y + z) (by linarith) (by linarith)
                have hw5 : (1922008203/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_711 (x + y + z) (by linarith) (by linarith)
                linarith
    · rcases le_total x (1063/1024:ℝ) with hc | hc
      · rcases le_total y (2041/1024:ℝ) with hc | hc
        · rcases le_total z (1083/1024:ℝ) with hc | hc
          · rcases le_total x (2121/2048:ℝ) with hc | hc
            · have hw0 : (1888462017/5000000000000:ℝ) ≤ wfun x := wc_15 x (by linarith) (by linarith)
              have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
              have hw3 : (235547/2000000000000:ℝ) ≤ wfun (x + y) := wc_243 (x + y) (by linarith) (by linarith)
              have hw4 : (161986357/5000000000000:ℝ) ≤ wfun (y + z) := wc_342 (y + z) (by linarith) (by linarith)
              have hw5 : (1424080951/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_650 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
              have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
              have hw3 : (5174037/5000000000000:ℝ) ≤ wfun (x + y) := wc_257 (x + y) (by linarith) (by linarith)
              have hw4 : (161986357/5000000000000:ℝ) ≤ wfun (y + z) := wc_342 (y + z) (by linarith) (by linarith)
              have hw5 : (1541044571/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_676 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_16 x (by linarith) (by linarith)
            have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
            have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
            have hw3 : (293481/2500000000000:ℝ) ≤ wfun (x + y) := wc_244 (x + y) (by linarith) (by linarith)
            have hw4 : (24610003/500000000000:ℝ) ≤ wfun (y + z) := wc_350 (y + z) (by linarith) (by linarith)
            have hw5 : (1658311191/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_691 (x + y + z) (by linarith) (by linarith)
            linarith
        · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_16 x (by linarith) (by linarith)
          have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
          have hw3 : (28474189/10000000000000:ℝ) ≤ wfun (x + y) := wc_272 (x + y) (by linarith) (by linarith)
          have hw4 : (489049523/10000000000000:ℝ) ≤ wfun (y + z) := wc_351 (y + z) (by linarith) (by linarith)
          have hw5 : (12893743/78125000000:ℝ) ≤ wfun (x + y + z) := wc_692 (x + y + z) (by linarith) (by linarith)
          linarith
      · rcases le_total y (2041/1024:ℝ) with hc | hc
        · rcases le_total z (1083/1024:ℝ) with hc | hc
          · rcases le_total x (2131/2048:ℝ) with hc | hc
            · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
              have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
              have hw3 : (7141617/2500000000000:ℝ) ≤ wfun (x + y) := wc_271 (x + y) (by linarith) (by linarith)
              have hw4 : (161986357/5000000000000:ℝ) ≤ wfun (y + z) := wc_342 (y + z) (by linarith) (by linarith)
              have hw5 : (66491401/400000000000:ℝ) ≤ wfun (x + y + z) := wc_690 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total y (4077/2048:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
                have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_127 y (by linarith) (by linarith)
                have hw3 : (55964847/10000000000000:ℝ) ≤ wfun (x + y) := wc_286 (x + y) (by linarith) (by linarith)
                have hw4 : (325017537/10000000000000:ℝ) ≤ wfun (y + z) := wc_341 (y + z) (by linarith) (by linarith)
                have hw5 : (1792041507/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_703 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
                have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_133 y (by linarith) (by linarith)
                have hw3 : (92247841/10000000000000:ℝ) ≤ wfun (x + y) := wc_300 (x + y) (by linarith) (by linarith)
                have hw4 : (405098789/10000000000000:ℝ) ≤ wfun (y + z) := wc_347 (y + z) (by linarith) (by linarith)
                have hw5 : (1922008203/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_711 (x + y + z) (by linarith) (by linarith)
                linarith
          · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
            have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
            have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
            have hw3 : (28474189/10000000000000:ℝ) ≤ wfun (x + y) := wc_272 (x + y) (by linarith) (by linarith)
            have hw4 : (24610003/500000000000:ℝ) ≤ wfun (y + z) := wc_350 (y + z) (by linarith) (by linarith)
            have hw5 : (1912837973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_713 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (1083/1024:ℝ) with hc | hc
          · rcases le_total x (2131/2048:ℝ) with hc | hc
            · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
              have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
              have hw3 : (22987523/2500000000000:ℝ) ≤ wfun (x + y) := wc_301 (x + y) (by linarith) (by linarith)
              have hw4 : (24610003/500000000000:ℝ) ≤ wfun (y + z) := wc_350 (y + z) (by linarith) (by linarith)
              have hw5 : (1917416231/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_712 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
              have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
              have hw3 : (2140811/156250000000:ℝ) ≤ wfun (x + y) := wc_321 (x + y) (by linarith) (by linarith)
              have hw4 : (24610003/500000000000:ℝ) ≤ wfun (y + z) := wc_350 (y + z) (by linarith) (by linarith)
              have hw5 : (410242943/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_724 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
            have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
            have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
            have hw3 : (11456693/1250000000000:ℝ) ≤ wfun (x + y) := wc_302 (x + y) (by linarith) (by linarith)
            have hw4 : (694482783/10000000000000:ℝ) ≤ wfun (y + z) := wc_354 (y + z) (by linarith) (by linarith)
            have hw5 : (272985599/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_728 (x + y + z) (by linarith) (by linarith)
            linarith
  · rcases le_total z (539/512:ℝ) with hc | hc
    · rcases le_total x (1063/1024:ℝ) with hc | hc
      · rcases le_total y (2051/1024:ℝ) with hc | hc
        · rcases le_total z (1073/1024:ℝ) with hc | hc
          · rcases le_total x (2121/2048:ℝ) with hc | hc
            · have hw0 : (1888462017/5000000000000:ℝ) ≤ wfun x := wc_15 x (by linarith) (by linarith)
              have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
                rcases le_total y (2:ℝ) with hq10 | hq10
                · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_140 y (by linarith) (by linarith))
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
              have hw3 : (22987523/2500000000000:ℝ) ≤ wfun (x + y) := wc_301 (x + y) (by linarith) (by linarith)
              have hw4 : (161986357/5000000000000:ℝ) ≤ wfun (y + z) := wc_342 (y + z) (by linarith) (by linarith)
              have hw5 : (1424080951/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_650 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
              have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
                rcases le_total y (2:ℝ) with hq10 | hq10
                · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_140 y (by linarith) (by linarith))
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
              have hw3 : (2140811/156250000000:ℝ) ≤ wfun (x + y) := wc_321 (x + y) (by linarith) (by linarith)
              have hw4 : (161986357/5000000000000:ℝ) ≤ wfun (y + z) := wc_342 (y + z) (by linarith) (by linarith)
              have hw5 : (1541044571/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_676 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_16 x (by linarith) (by linarith)
            have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
              rcases le_total y (2:ℝ) with hq10 | hq10
              · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_140 y (by linarith) (by linarith))
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
            have hw3 : (11456693/1250000000000:ℝ) ≤ wfun (x + y) := wc_302 (x + y) (by linarith) (by linarith)
            have hw4 : (24610003/500000000000:ℝ) ≤ wfun (y + z) := wc_350 (y + z) (by linarith) (by linarith)
            have hw5 : (1658311191/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_691 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (1073/1024:ℝ) with hc | hc
          · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_16 x (by linarith) (by linarith)
            have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
            have hw3 : (190300253/10000000000000:ℝ) ≤ wfun (x + y) := wc_328 (x + y) (by linarith) (by linarith)
            have hw4 : (24610003/500000000000:ℝ) ≤ wfun (y + z) := wc_350 (y + z) (by linarith) (by linarith)
            have hw5 : (1658311191/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_691 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_16 x (by linarith) (by linarith)
            have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
            have hw3 : (190300253/10000000000000:ℝ) ≤ wfun (x + y) := wc_328 (x + y) (by linarith) (by linarith)
            have hw4 : (694482783/10000000000000:ℝ) ≤ wfun (y + z) := wc_354 (y + z) (by linarith) (by linarith)
            have hw5 : (1912837973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_713 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total y (2051/1024:ℝ) with hc | hc
        · rcases le_total z (1073/1024:ℝ) with hc | hc
          · rcases le_total x (2131/2048:ℝ) with hc | hc
            · rcases le_total y (4097/2048:ℝ) with hc | hc
              · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
                have hw1 : (1591808227/10000000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (2:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_139 y (by linarith) (by linarith))
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
                have hw3 : (23941523/1250000000000:ℝ) ≤ wfun (x + y) := wc_326 (x + y) (by linarith) (by linarith)
                have hw4 : (325017537/10000000000000:ℝ) ≤ wfun (y + z) := wc_341 (y + z) (by linarith) (by linarith)
                have hw5 : (1666270777/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_689 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
                have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
                have hw3 : (25442213/1000000000000:ℝ) ≤ wfun (x + y) := wc_334 (x + y) (by linarith) (by linarith)
                have hw4 : (405098789/10000000000000:ℝ) ≤ wfun (y + z) := wc_347 (y + z) (by linarith) (by linarith)
                have hw5 : (1792041507/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_703 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (4097/2048:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
                have hw1 : (1591808227/10000000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (2:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_139 y (by linarith) (by linarith))
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
                have hw3 : (25442213/1000000000000:ℝ) ≤ wfun (x + y) := wc_334 (x + y) (by linarith) (by linarith)
                have hw4 : (325017537/10000000000000:ℝ) ≤ wfun (y + z) := wc_341 (y + z) (by linarith) (by linarith)
                have hw5 : (1792041507/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_703 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
                have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
                have hw3 : (326066581/10000000000000:ℝ) ≤ wfun (x + y) := wc_340 (x + y) (by linarith) (by linarith)
                have hw4 : (405098789/10000000000000:ℝ) ≤ wfun (y + z) := wc_347 (y + z) (by linarith) (by linarith)
                have hw5 : (1922008203/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_711 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (2131/2048:ℝ) with hc | hc
            · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
              have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
                rcases le_total y (2:ℝ) with hq10 | hq10
                · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_140 y (by linarith) (by linarith))
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
              have hw3 : (7636599/400000000000:ℝ) ≤ wfun (x + y) := wc_327 (x + y) (by linarith) (by linarith)
              have hw4 : (24610003/500000000000:ℝ) ≤ wfun (y + z) := wc_350 (y + z) (by linarith) (by linarith)
              have hw5 : (1917416231/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_712 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
              have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
                rcases le_total y (2:ℝ) with hq10 | hq10
                · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_140 y (by linarith) (by linarith))
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
              have hw3 : (63400731/2500000000000:ℝ) ≤ wfun (x + y) := wc_335 (x + y) (by linarith) (by linarith)
              have hw4 : (24610003/500000000000:ℝ) ≤ wfun (y + z) := wc_350 (y + z) (by linarith) (by linarith)
              have hw5 : (410242943/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_724 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (1073/1024:ℝ) with hc | hc
          · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
            have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
            have hw3 : (161986357/5000000000000:ℝ) ≤ wfun (x + y) := wc_342 (x + y) (by linarith) (by linarith)
            have hw4 : (24610003/500000000000:ℝ) ≤ wfun (y + z) := wc_350 (y + z) (by linarith) (by linarith)
            have hw5 : (1912837973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_713 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
            have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
            have hw3 : (161986357/5000000000000:ℝ) ≤ wfun (x + y) := wc_342 (x + y) (by linarith) (by linarith)
            have hw4 : (694482783/10000000000000:ℝ) ≤ wfun (y + z) := wc_354 (y + z) (by linarith) (by linarith)
            have hw5 : (272985599/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_728 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total x (1063/1024:ℝ) with hc | hc
      · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_16 x (by linarith) (by linarith)
        have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
          rcases le_total y (2:ℝ) with hq10 | hq10
          · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
        have hw3 : (91064031/10000000000000:ℝ) ≤ wfun (x + y) := wc_303 (x + y) (by linarith) (by linarith)
        have hw4 : (685641829/10000000000000:ℝ) ≤ wfun (y + z) := wc_356 (y + z) (by linarith) (by linarith)
        have hw5 : (947330549/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_715 (x + y + z) (by linarith) (by linarith)
        linarith
      · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
        have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
          rcases le_total y (2:ℝ) with hq10 | hq10
          · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
        have hw3 : (189078223/10000000000000:ℝ) ≤ wfun (x + y) := wc_329 (x + y) (by linarith) (by linarith)
        have hw4 : (685641829/10000000000000:ℝ) ≤ wfun (y + z) := wc_356 (y + z) (by linarith) (by linarith)
        have hw5 : (216315697/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_730 (x + y + z) (by linarith) (by linarith)
        linarith

set_option maxHeartbeats 20000000 in
lemma ch_59 (x y z : ℝ) (hx1 : (63/64:ℝ) ≤ x) (hx2 : x ≤ (73/64:ℝ))
    (hy1 : (131/64:ℝ) ≤ y) (hy2 : y ≤ (141/64:ℝ))
    (hz1 : (121/64:ℝ) ≤ z) (hz2 : z ≤ (141/64:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total z (131/64:ℝ) with hc | hc
  · rcases le_total x (17/16:ℝ) with hc | hc
    · rcases le_total y (17/8:ℝ) with hc | hc
      · rcases le_total z (63/32:ℝ) with hc | hc
        · have hw1 : (42177537/1000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
          have hw2 : (795663039/1250000000000:ℝ) ≤ wfun z := wc_76 z (by linarith) (by linarith)
          have hw3 : (75856633/10000000000000:ℝ) ≤ wfun (x + y) := wc_311 (x + y) (by linarith) (by linarith)
          linarith
        · rcases le_total x (131/128:ℝ) with hc | hc
          · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := by
              rcases le_total x (1:ℝ) with hq00 | hq00
              · exact le_trans (by norm_num) (wc_5 x (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_7 x (by linarith) (by linarith))
            have hw1 : (42177537/1000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
            have hw3 : (79711817/10000000000000:ℝ) ≤ wfun (x + y) := wc_310 (x + y) (by linarith) (by linarith)
            have hw4 : (56143/10000000000000:ℝ) ≤ wfun (y + z) := wc_459 (y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total y (267/128:ℝ) with hc | hc
            · rcases le_total z (257/128:ℝ) with hc | hc
              · rcases le_total x (267/256:ℝ) with hc | hc
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
                  have hw1 : (18186303/400000000000:ℝ) ≤ wfun y := wc_156 y (by linarith) (by linarith)
                  have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                    rcases le_total z (2:ℝ) with hq20 | hq20
                    · exact le_trans (by norm_num) (wc_90 z (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                  have hw3 : (215107179/1250000000000:ℝ) ≤ wfun (x + y) := wc_371 (x + y) (by linarith) (by linarith)
                  have hw4 : (60567/10000000000000:ℝ) ≤ wfun (y + z) := wc_456 (y + z) (by linarith) (by linarith)
                  have hw5 : (90750063/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_812 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw1 : (18186303/400000000000:ℝ) ≤ wfun y := wc_156 y (by linarith) (by linarith)
                  have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                    rcases le_total z (2:ℝ) with hq20 | hq20
                    · exact le_trans (by norm_num) (wc_90 z (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                  have hw3 : (1629257293/5000000000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
                  have hw4 : (60567/10000000000000:ℝ) ≤ wfun (y + z) := wc_456 (y + z) (by linarith) (by linarith)
                  have hw5 : (534939039/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_885 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw1 : (18186303/400000000000:ℝ) ≤ wfun y := wc_156 y (by linarith) (by linarith)
                have hw3 : (419583999/2500000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
                have hw4 : (24278963/400000000000:ℝ) ≤ wfun (y + z) := wc_552 (y + z) (by linarith) (by linarith)
                have hw5 : (1048517003/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_949 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw1 : (4789633321/10000000000000:ℝ) ≤ wfun y := wc_172 y (by linarith) (by linarith)
              have hw3 : (5096134953/10000000000000:ℝ) ≤ wfun (x + y) := wc_384 (x + y) (by linarith) (by linarith)
              have hw4 : (913271/15625000000:ℝ) ≤ wfun (y + z) := wc_554 (y + z) (by linarith) (by linarith)
              have hw5 : (1017509707/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_950 (x + y + z) (by linarith) (by linarith)
              linarith
      · have hw1 : (48584483/40000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
        have hw3 : (589186081/1250000000000:ℝ) ≤ wfun (x + y) := by
          rcases le_total (x + y) (13/4:ℝ) with hq30 | hq30
          · exact le_trans (by norm_num) (wc_386 (x + y) (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_389 (x + y) (by linarith) (by linarith))
        have hw4 : (13029/2500000000000:ℝ) ≤ wfun (y + z) := wc_460 (y + z) (by linarith) (by linarith)
        linarith
    · have hw0 : (15429929/1000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
      have hw1 : (182240171/5000000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
      have hw3 : (589186081/1250000000000:ℝ) ≤ wfun (x + y) := by
        rcases le_total (x + y) (13/4:ℝ) with hq30 | hq30
        · exact le_trans (by norm_num) (wc_386 (x + y) (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_392 (x + y) (by linarith) (by linarith))
      linarith
  · have hw1 : (182240171/5000000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
    have hw2 : (182240171/5000000000000:ℝ) ≤ wfun z := wc_160 z (by linarith) (by linarith)
    have hw3 : (17540223/2500000000000:ℝ) ≤ wfun (x + y) := by
      rcases le_total (x + y) (13/4:ℝ) with hq30 | hq30
      · exact le_trans (by norm_num) (wc_312 (x + y) (by linarith) (by linarith))
      exact le_trans (by norm_num) (wc_392 (x + y) (by linarith) (by linarith))
    have hw4 : (2156990541/10000000000000:ℝ) ≤ wfun (y + z) := by
      rcases le_total (y + z) (17/4:ℝ) with hq40 | hq40
      · exact le_trans (by norm_num) (wc_742 (y + z) (by linarith) (by linarith))
      exact le_trans (by norm_num) (wc_758 (y + z) (by linarith) (by linarith))
    have hw5 : (502714163/5000000000000:ℝ) ≤ wfun (x + y + z) := by
      rcases le_total (x + y + z) (21/4:ℝ) with hq50 | hq50
      · exact le_trans (by norm_num) (wc_951 (x + y + z) (by linarith) (by linarith))
      rcases le_total (x + y + z) (11/2:ℝ) with hq51 | hq51
      · exact le_trans (by norm_num) (wc_980 (x + y + z) (by linarith) (by linarith))
      exact le_trans (by norm_num) (wc_981 (x + y + z) (by linarith) (by linarith))
    linarith

set_option maxHeartbeats 20000000 in
lemma ch_63 (x y z : ℝ) (hx1 : (63/64:ℝ) ≤ x) (hx2 : x ≤ (17/16:ℝ))
    (hy1 : (1525/512:ℝ) ≤ y) (hy2 : y ≤ (389/128:ℝ))
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
    linarith
  · rcases le_total z (131/128:ℝ) with hc | hc
    · have hw2 : (2370342229/2500000000000:ℝ) ≤ wfun z := by
        rcases le_total z (1:ℝ) with hq20 | hq20
        · exact le_trans (by norm_num) (wc_5 z (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_7 z (by linarith) (by linarith))
      linarith
    · rcases le_total y (3081/1024:ℝ) with hc | hc
      · rcases le_total x (267/256:ℝ) with hc | hc
        · rcases le_total z (267/256:ℝ) with hc | hc
          · rcases le_total y (6131/2048:ℝ) with hc | hc
            · rcases le_total x (529/512:ℝ) with hc | hc
              · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
                have hw1 : (137922559/2500000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_13 z (by linarith) (by linarith)
                have hw5 : (45928559/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_780 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total z (529/512:ℝ) with hc | hc
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
                  have hw1 : (137922559/2500000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                  have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
                  have hw5 : (139560919/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_799 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
                  have hw1 : (137922559/2500000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
                  have hw5 : (282019961/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_832 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total x (529/512:ℝ) with hc | hc
              · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
                have hw1 : (102076243/10000000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (3:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_216 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_220 y (by linarith) (by linarith))
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_13 z (by linarith) (by linarith)
                have hw3 : (36159/250000000000:ℝ) ≤ wfun (x + y) := wc_466 (x + y) (by linarith) (by linarith)
                have hw4 : (1432423/10000000000000:ℝ) ≤ wfun (y + z) := wc_467 (y + z) (by linarith) (by linarith)
                have hw5 : (42053501/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_817 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
                have hw1 : (102076243/10000000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (3:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_216 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_220 y (by linarith) (by linarith))
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_13 z (by linarith) (by linarith)
                have hw3 : (6897/1220703125:ℝ) ≤ wfun (x + y) := wc_497 (x + y) (by linarith) (by linarith)
                have hw4 : (1432423/10000000000000:ℝ) ≤ wfun (y + z) := wc_467 (y + z) (by linarith) (by linarith)
                have hw5 : (189012269/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_852 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (6131/2048:ℝ) with hc | hc
            · rcases le_total x (529/512:ℝ) with hc | hc
              · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
                have hw1 : (137922559/2500000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                have hw4 : (8115287/5000000000000:ℝ) ≤ wfun (y + z) := wc_482 (y + z) (by linarith) (by linarith)
                have hw5 : (55971473/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_833 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total z (539/512:ℝ) with hc | hc
                · rcases le_total y (12231/4096:ℝ) with hc | hc
                  · rcases le_total x (1063/1024:ℝ) with hc | hc
                    · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_16 x (by linarith) (by linarith)
                      have hw1 : (183106839/2000000000000:ℝ) ≤ wfun y := wc_210 y (by linarith) (by linarith)
                      have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                      have hw4 : (16511887/10000000000000:ℝ) ≤ wfun (y + z) := wc_480 (y + z) (by linarith) (by linarith)
                      have hw5 : (238608519/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_866 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
                      have hw1 : (183106839/2000000000000:ℝ) ≤ wfun y := wc_210 y (by linarith) (by linarith)
                      have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                      have hw3 : (198721/2500000000000:ℝ) ≤ wfun (x + y) := wc_465 (x + y) (by linarith) (by linarith)
                      have hw4 : (16511887/10000000000000:ℝ) ≤ wfun (y + z) := wc_480 (y + z) (by linarith) (by linarith)
                      have hw5 : (147807153/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_891 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
                    have hw1 : (5534703/100000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
                    have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                    have hw3 : (1737357/2500000000000:ℝ) ≤ wfun (x + y) := wc_472 (x + y) (by linarith) (by linarith)
                    have hw4 : (5024187/625000000000:ℝ) ≤ wfun (y + z) := wc_500 (y + z) (by linarith) (by linarith)
                    have hw5 : (82047199/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_899 (x + y + z) (by linarith) (by linarith)
                    linarith
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
                  have hw1 : (137922559/2500000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                  have hw4 : (428161/40000000000:ℝ) ≤ wfun (y + z) := wc_503 (y + z) (by linarith) (by linarith)
                  have hw5 : (709888559/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_909 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total x (529/512:ℝ) with hc | hc
              · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
                have hw1 : (102076243/10000000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (3:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_216 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_220 y (by linarith) (by linarith))
                have hw3 : (36159/250000000000:ℝ) ≤ wfun (x + y) := wc_466 (x + y) (by linarith) (by linarith)
                have hw4 : (188423087/10000000000000:ℝ) ≤ wfun (y + z) := wc_517 (y + z) (by linarith) (by linarith)
                have hw5 : (592818281/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_893 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
                have hw1 : (102076243/10000000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (3:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_216 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_220 y (by linarith) (by linarith))
                have hw3 : (6897/1220703125:ℝ) ≤ wfun (x + y) := wc_497 (x + y) (by linarith) (by linarith)
                have hw4 : (188423087/10000000000000:ℝ) ≤ wfun (y + z) := wc_517 (y + z) (by linarith) (by linarith)
                have hw5 : (853292617/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_931 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (267/256:ℝ) with hc | hc
          · rcases le_total y (6131/2048:ℝ) with hc | hc
            · rcases le_total x (539/512:ℝ) with hc | hc
              · rcases le_total z (529/512:ℝ) with hc | hc
                · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                  have hw1 : (137922559/2500000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                  have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
                  have hw3 : (4097079/2500000000000:ℝ) ≤ wfun (x + y) := wc_481 (x + y) (by linarith) (by linarith)
                  have hw5 : (282019961/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_832 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total y (12231/4096:ℝ) with hc | hc
                  · rcases le_total x (1073/1024:ℝ) with hc | hc
                    · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                      have hw1 : (183106839/2000000000000:ℝ) ≤ wfun y := wc_210 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
                      have hw3 : (16592229/10000000000000:ℝ) ≤ wfun (x + y) := wc_479 (x + y) (by linarith) (by linarith)
                      have hw5 : (238608519/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_866 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                      have hw1 : (183106839/2000000000000:ℝ) ≤ wfun y := wc_210 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
                      have hw3 : (52510613/10000000000000:ℝ) ≤ wfun (x + y) := wc_496 (x + y) (by linarith) (by linarith)
                      have hw5 : (147807153/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_891 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                    have hw1 : (5534703/100000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
                    have hw3 : (5024187/625000000000:ℝ) ≤ wfun (x + y) := wc_500 (x + y) (by linarith) (by linarith)
                    have hw4 : (1737357/2500000000000:ℝ) ≤ wfun (y + z) := wc_472 (y + z) (by linarith) (by linarith)
                    have hw5 : (82047199/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_899 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total z (529/512:ℝ) with hc | hc
                · have hw1 : (137922559/2500000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                  have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
                  have hw3 : (428161/40000000000:ℝ) ≤ wfun (x + y) := wc_503 (x + y) (by linarith) (by linarith)
                  have hw5 : (236277491/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_867 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw1 : (137922559/2500000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
                  have hw3 : (428161/40000000000:ℝ) ≤ wfun (x + y) := wc_503 (x + y) (by linarith) (by linarith)
                  have hw5 : (709888559/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_909 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total x (539/512:ℝ) with hc | hc
              · rcases le_total z (529/512:ℝ) with hc | hc
                · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                  have hw1 : (102076243/10000000000000:ℝ) ≤ wfun y := by
                    rcases le_total y (3:ℝ) with hq10 | hq10
                    · exact le_trans (by norm_num) (wc_216 y (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_220 y (by linarith) (by linarith))
                  have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
                  have hw3 : (95123723/5000000000000:ℝ) ≤ wfun (x + y) := wc_516 (x + y) (by linarith) (by linarith)
                  have hw4 : (36159/250000000000:ℝ) ≤ wfun (y + z) := wc_466 (y + z) (by linarith) (by linarith)
                  have hw5 : (298692789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_892 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                  have hw1 : (102076243/10000000000000:ℝ) ≤ wfun y := by
                    rcases le_total y (3:ℝ) with hq10 | hq10
                    · exact le_trans (by norm_num) (wc_216 y (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_220 y (by linarith) (by linarith))
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
                  have hw3 : (95123723/5000000000000:ℝ) ≤ wfun (x + y) := wc_516 (x + y) (by linarith) (by linarith)
                  have hw4 : (6897/1220703125:ℝ) ≤ wfun (y + z) := wc_497 (y + z) (by linarith) (by linarith)
                  have hw5 : (429927023/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_930 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw1 : (102076243/10000000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (3:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_216 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_220 y (by linarith) (by linarith))
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_13 z (by linarith) (by linarith)
                have hw3 : (200521187/5000000000000:ℝ) ≤ wfun (x + y) := wc_533 (x + y) (by linarith) (by linarith)
                have hw4 : (1432423/10000000000000:ℝ) ≤ wfun (y + z) := wc_467 (y + z) (by linarith) (by linarith)
                have hw5 : (853292617/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_931 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (6131/2048:ℝ) with hc | hc
            · rcases le_total x (539/512:ℝ) with hc | hc
              · rcases le_total z (539/512:ℝ) with hc | hc
                · rcases le_total y (12231/4096:ℝ) with hc | hc
                  · rcases le_total x (1073/1024:ℝ) with hc | hc
                    · rcases le_total z (1073/1024:ℝ) with hc | hc
                      · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                        have hw1 : (183106839/2000000000000:ℝ) ≤ wfun y := wc_210 y (by linarith) (by linarith)
                        have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
                        have hw3 : (16592229/10000000000000:ℝ) ≤ wfun (x + y) := wc_479 (x + y) (by linarith) (by linarith)
                        have hw4 : (16592229/10000000000000:ℝ) ≤ wfun (y + z) := wc_479 (y + z) (by linarith) (by linarith)
                        have hw5 : (359821577/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_908 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                        have hw1 : (183106839/2000000000000:ℝ) ≤ wfun y := wc_210 y (by linarith) (by linarith)
                        have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
                        have hw3 : (16592229/10000000000000:ℝ) ≤ wfun (x + y) := wc_479 (x + y) (by linarith) (by linarith)
                        have hw4 : (52510613/10000000000000:ℝ) ≤ wfun (y + z) := wc_496 (y + z) (by linarith) (by linarith)
                        have hw5 : (214317369/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_929 (x + y + z) (by linarith) (by linarith)
                        linarith
                    · rcases le_total z (1073/1024:ℝ) with hc | hc
                      · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                        have hw1 : (183106839/2000000000000:ℝ) ≤ wfun y := wc_210 y (by linarith) (by linarith)
                        have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
                        have hw3 : (52510613/10000000000000:ℝ) ≤ wfun (x + y) := wc_496 (x + y) (by linarith) (by linarith)
                        have hw4 : (16592229/10000000000000:ℝ) ≤ wfun (y + z) := wc_479 (y + z) (by linarith) (by linarith)
                        have hw5 : (214317369/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_929 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                        have hw1 : (183106839/2000000000000:ℝ) ≤ wfun y := wc_210 y (by linarith) (by linarith)
                        have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
                        have hw3 : (52510613/10000000000000:ℝ) ≤ wfun (x + y) := wc_496 (x + y) (by linarith) (by linarith)
                        have hw4 : (52510613/10000000000000:ℝ) ≤ wfun (y + z) := wc_496 (y + z) (by linarith) (by linarith)
                        have hw5 : (251547891/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_939 (x + y + z) (by linarith) (by linarith)
                        linarith
                  · rcases le_total x (1073/1024:ℝ) with hc | hc
                    · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                      have hw1 : (5534703/100000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
                      have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                      have hw3 : (80777393/10000000000000:ℝ) ≤ wfun (x + y) := wc_499 (x + y) (by linarith) (by linarith)
                      have hw4 : (5024187/625000000000:ℝ) ≤ wfun (y + z) := wc_500 (y + z) (by linarith) (by linarith)
                      have hw5 : (23354863/250000000000:ℝ) ≤ wfun (x + y + z) := wc_935 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                      have hw1 : (5534703/100000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
                      have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                      have hw3 : (36879733/2500000000000:ℝ) ≤ wfun (x + y) := wc_506 (x + y) (by linarith) (by linarith)
                      have hw4 : (5024187/625000000000:ℝ) ≤ wfun (y + z) := wc_500 (y + z) (by linarith) (by linarith)
                      have hw5 : (13608131/125000000000:ℝ) ≤ wfun (x + y + z) := wc_944 (x + y + z) (by linarith) (by linarith)
                      linarith
                · rcases le_total y (12231/4096:ℝ) with hc | hc
                  · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                    have hw1 : (183106839/2000000000000:ℝ) ≤ wfun y := wc_210 y (by linarith) (by linarith)
                    have hw3 : (16511887/10000000000000:ℝ) ≤ wfun (x + y) := wc_480 (x + y) (by linarith) (by linarith)
                    have hw4 : (107845387/10000000000000:ℝ) ≤ wfun (y + z) := wc_502 (y + z) (by linarith) (by linarith)
                    have hw5 : (499246979/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_940 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                    have hw1 : (5534703/100000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
                    have hw3 : (5024187/625000000000:ℝ) ≤ wfun (x + y) := wc_500 (x + y) (by linarith) (by linarith)
                    have hw4 : (14547321/625000000000:ℝ) ≤ wfun (y + z) := wc_518 (y + z) (by linarith) (by linarith)
                    have hw5 : (1249238179/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_955 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total z (539/512:ℝ) with hc | hc
                · rcases le_total y (12231/4096:ℝ) with hc | hc
                  · have hw1 : (183106839/2000000000000:ℝ) ≤ wfun y := wc_210 y (by linarith) (by linarith)
                    have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                    have hw3 : (107845387/10000000000000:ℝ) ≤ wfun (x + y) := wc_502 (x + y) (by linarith) (by linarith)
                    have hw4 : (16511887/10000000000000:ℝ) ≤ wfun (y + z) := wc_480 (y + z) (by linarith) (by linarith)
                    have hw5 : (499246979/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_940 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw1 : (5534703/100000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
                    have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                    have hw3 : (14547321/625000000000:ℝ) ≤ wfun (x + y) := wc_518 (x + y) (by linarith) (by linarith)
                    have hw4 : (5024187/625000000000:ℝ) ≤ wfun (y + z) := wc_500 (y + z) (by linarith) (by linarith)
                    have hw5 : (1249238179/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_955 (x + y + z) (by linarith) (by linarith)
                    linarith
                · have hw1 : (137922559/2500000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                  have hw3 : (428161/40000000000:ℝ) ≤ wfun (x + y) := wc_503 (x + y) (by linarith) (by linarith)
                  have hw4 : (428161/40000000000:ℝ) ≤ wfun (y + z) := wc_503 (y + z) (by linarith) (by linarith)
                  have hw5 : (1319026531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total x (539/512:ℝ) with hc | hc
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                have hw1 : (102076243/10000000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (3:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_216 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_220 y (by linarith) (by linarith))
                have hw3 : (95123723/5000000000000:ℝ) ≤ wfun (x + y) := wc_516 (x + y) (by linarith) (by linarith)
                have hw4 : (188423087/10000000000000:ℝ) ≤ wfun (y + z) := wc_517 (y + z) (by linarith) (by linarith)
                have hw5 : (578965893/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_954 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw1 : (102076243/10000000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (3:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_216 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_220 y (by linarith) (by linarith))
                have hw3 : (200521187/5000000000000:ℝ) ≤ wfun (x + y) := wc_533 (x + y) (by linarith) (by linarith)
                have hw4 : (188423087/10000000000000:ℝ) ≤ wfun (y + z) := wc_517 (y + z) (by linarith) (by linarith)
                have hw5 : (1505067239/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_963 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total x (267/256:ℝ) with hc | hc
        · rcases le_total z (267/256:ℝ) with hc | hc
          · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
            have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_13 z (by linarith) (by linarith)
            have hw3 : (58750599/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
            have hw4 : (58750599/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
            have hw5 : (480942433/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_869 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
            have hw3 : (58750599/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
            have hw4 : (267941559/5000000000000:ℝ) ≤ wfun (y + z) := wc_539 (y + z) (by linarith) (by linarith)
            have hw5 : (199185017/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_941 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (267/256:ℝ) with hc | hc
          · have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_13 z (by linarith) (by linarith)
            have hw3 : (267941559/5000000000000:ℝ) ≤ wfun (x + y) := wc_539 (x + y) (by linarith) (by linarith)
            have hw4 : (58750599/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
            have hw5 : (199185017/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_941 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw3 : (267941559/5000000000000:ℝ) ≤ wfun (x + y) := wc_539 (x + y) (by linarith) (by linarith)
            have hw4 : (267941559/5000000000000:ℝ) ≤ wfun (y + z) := wc_539 (y + z) (by linarith) (by linarith)
            have hw5 : (1680579671/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_964 (x + y + z) (by linarith) (by linarith)
            linarith

end Zeta23Ext.Bridge.FourPoint
