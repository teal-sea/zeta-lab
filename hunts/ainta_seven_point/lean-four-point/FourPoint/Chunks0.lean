import FourPoint.Cells

/-! Chunk module 0 of 16 of the three-dimensional table.  Each lemma is one
subtree of at most 110 leaves of one box's bisection tree; `FourPoint/Boxes.lean` routes
the box down to them.  Cutting the tree this way gives each subtree its own
heartbeat budget and lets `lake` compile them in parallel. -/

noncomputable section
namespace Zeta23Ext.Bridge.FourPoint

set_option maxHeartbeats 20000000 in
lemma ch_17 (x y z : ℝ) (hx1 : (267/256:ℝ) ≤ x) (hx2 : x ≤ (539/512:ℝ))
    (hy1 : (63/32:ℝ) ≤ y) (hy2 : y ≤ (1013/512:ℝ))
    (hz1 : (131/128:ℝ) ≤ z) (hz2 : z ≤ (267/256:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total z (529/512:ℝ) with hc | hc
  · rcases le_total x (1073/1024:ℝ) with hc | hc
    · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
      have hw1 : (4884069333/10000000000000:ℝ) ≤ wfun y := wc_88 y (by linarith) (by linarith)
      have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
      have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := by
        rcases le_total (y + z) (3:ℝ) with hq40 | hq40
        · exact le_trans (by norm_num) (wc_215 (y + z) (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_221 (y + z) (by linarith) (by linarith))
      have hw5 : (165310021/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_508 (x + y + z) (by linarith) (by linarith)
      linarith
    · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
      have hw1 : (4884069333/10000000000000:ℝ) ≤ wfun y := wc_88 y (by linarith) (by linarith)
      have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
      have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := by
        rcases le_total (y + z) (3:ℝ) with hq40 | hq40
        · exact le_trans (by norm_num) (wc_215 (y + z) (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_221 (y + z) (by linarith) (by linarith))
      have hw5 : (255477031/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_521 (x + y + z) (by linarith) (by linarith)
      linarith
  · rcases le_total x (1073/1024:ℝ) with hc | hc
    · rcases le_total y (2021/1024:ℝ) with hc | hc
      · rcases le_total z (1063/1024:ℝ) with hc | hc
        · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
          have hw1 : (2946158453/5000000000000:ℝ) ≤ wfun y := wc_87 y (by linarith) (by linarith)
          have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
          have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := wc_223 (y + z) (by linarith) (by linarith)
          have hw5 : (184146301/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_527 (x + y + z) (by linarith) (by linarith)
          linarith
        · rcases le_total x (2141/2048:ℝ) with hc | hc
          · rcases le_total y (4037/2048:ℝ) with hc | hc
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_28 x (by linarith) (by linarith)
              have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_86 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
              have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_231 (x + y) (by linarith) (by linarith)
              have hw4 : (3586667/1250000000000:ℝ) ≤ wfun (y + z) := wc_227 (y + z) (by linarith) (by linarith)
              have hw5 : (20003551/400000000000:ℝ) ≤ wfun (x + y + z) := wc_535 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_28 x (by linarith) (by linarith)
              have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_92 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
              have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_234 (x + y) (by linarith) (by linarith)
              have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_230 (y + z) (by linarith) (by linarith)
              have hw5 : (572192259/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_540 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (4037/2048:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_86 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
              have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_234 (x + y) (by linarith) (by linarith)
              have hw4 : (3586667/1250000000000:ℝ) ≤ wfun (y + z) := wc_227 (y + z) (by linarith) (by linarith)
              have hw5 : (572192259/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_540 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (2131/2048:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
                have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_92 y (by linarith) (by linarith)
                have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
                have hw4 : (3586667/1250000000000:ℝ) ≤ wfun (y + z) := wc_229 (y + z) (by linarith) (by linarith)
                have hw5 : (162636919/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_542 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
                have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_92 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_231 (y + z) (by linarith) (by linarith)
                have hw5 : (183045519/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_557 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total z (1063/1024:ℝ) with hc | hc
        · rcases le_total x (2141/2048:ℝ) with hc | hc
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_28 x (by linarith) (by linarith)
            have hw1 : (4902043129/10000000000000:ℝ) ≤ wfun y := wc_96 y (by linarith) (by linarith)
            have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
            have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_228 (y + z) (by linarith) (by linarith)
            have hw5 : (498883881/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_536 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total y (4047/2048:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_95 y (by linarith) (by linarith)
              have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
              have hw4 : (3586667/1250000000000:ℝ) ≤ wfun (y + z) := wc_227 (y + z) (by linarith) (by linarith)
              have hw5 : (572192259/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_540 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_99 y (by linarith) (by linarith)
              have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
              have hw3 : (1181561/10000000000000:ℝ) ≤ wfun (x + y) := wc_242 (x + y) (by linarith) (by linarith)
              have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_230 (y + z) (by linarith) (by linarith)
              have hw5 : (648981217/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_543 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (2141/2048:ℝ) with hc | hc
          · rcases le_total y (4047/2048:ℝ) with hc | hc
            · rcases le_total z (2131/2048:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_28 x (by linarith) (by linarith)
                have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_95 y (by linarith) (by linarith)
                have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
                have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_231 (y + z) (by linarith) (by linarith)
                have hw5 : (162636919/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_542 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_28 x (by linarith) (by linarith)
                have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_95 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_234 (y + z) (by linarith) (by linarith)
                have hw5 : (183045519/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_557 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (2131/2048:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_28 x (by linarith) (by linarith)
                have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_99 y (by linarith) (by linarith)
                have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
                have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_234 (y + z) (by linarith) (by linarith)
                have hw5 : (183045519/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_557 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total x (4277/4096:ℝ) with hc | hc
                · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
                  have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_99 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                  have hw5 : (81942717/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_559 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total y (8099/4096:ℝ) with hc | hc
                  · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
                    have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                    have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_237 (x + y) (by linarith) (by linarith)
                    have hw5 : (865374359/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_567 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
                    have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                    have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_240 (x + y) (by linarith) (by linarith)
                    have hw5 : (227869559/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_569 (x + y + z) (by linarith) (by linarith)
                    linarith
          · rcases le_total y (4047/2048:ℝ) with hc | hc
            · rcases le_total z (2131/2048:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
                have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_95 y (by linarith) (by linarith)
                have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
                have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_231 (y + z) (by linarith) (by linarith)
                have hw5 : (183045519/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_557 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total x (4287/4096:ℝ) with hc | hc
                · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
                  have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_95 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                  have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_234 (y + z) (by linarith) (by linarith)
                  have hw5 : (81942717/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_559 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
                  have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_95 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                  have hw3 : (41/1250000000000:ℝ) ≤ wfun (x + y) := wc_238 (x + y) (by linarith) (by linarith)
                  have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_234 (y + z) (by linarith) (by linarith)
                  have hw5 : (864332647/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_568 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total z (2131/2048:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
                have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_99 y (by linarith) (by linarith)
                have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
                have hw3 : (1181561/10000000000000:ℝ) ≤ wfun (x + y) := wc_242 (x + y) (by linarith) (by linarith)
                have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_234 (y + z) (by linarith) (by linarith)
                have hw5 : (12788137/156250000000:ℝ) ≤ wfun (x + y + z) := wc_560 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total x (4287/4096:ℝ) with hc | hc
                · rcases le_total y (8099/4096:ℝ) with hc | hc
                  · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
                    have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                    have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_240 (x + y) (by linarith) (by linarith)
                    have hw5 : (227869559/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_569 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
                    have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                    have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_250 (x + y) (by linarith) (by linarith)
                    have hw5 : (958721819/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_576 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total y (8099/4096:ℝ) with hc | hc
                  · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
                    have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                    have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_250 (x + y) (by linarith) (by linarith)
                    have hw5 : (958721819/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_576 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
                    have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                    have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_254 (x + y) (by linarith) (by linarith)
                    have hw5 : (1007100179/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_579 (x + y + z) (by linarith) (by linarith)
                    linarith
    · rcases le_total y (2021/1024:ℝ) with hc | hc
      · rcases le_total z (1063/1024:ℝ) with hc | hc
        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
          have hw1 : (2946158453/5000000000000:ℝ) ≤ wfun y := wc_87 y (by linarith) (by linarith)
          have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
          have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := wc_223 (y + z) (by linarith) (by linarith)
          have hw5 : (99536523/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_537 (x + y + z) (by linarith) (by linarith)
          linarith
        · rcases le_total x (2151/2048:ℝ) with hc | hc
          · rcases le_total y (4037/2048:ℝ) with hc | hc
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_86 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
              have hw4 : (3586667/1250000000000:ℝ) ≤ wfun (y + z) := wc_227 (y + z) (by linarith) (by linarith)
              have hw5 : (648981217/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_543 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (2131/2048:ℝ) with hc | hc
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_92 y (by linarith) (by linarith)
                have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
                have hw4 : (3586667/1250000000000:ℝ) ≤ wfun (y + z) := wc_229 (y + z) (by linarith) (by linarith)
                have hw5 : (183045519/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_557 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_92 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_231 (y + z) (by linarith) (by linarith)
                have hw5 : (12788137/156250000000:ℝ) ≤ wfun (x + y + z) := wc_560 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (4037/2048:ℝ) with hc | hc
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_86 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
              have hw4 : (3586667/1250000000000:ℝ) ≤ wfun (y + z) := wc_227 (y + z) (by linarith) (by linarith)
              have hw5 : (730420113/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_558 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (2131/2048:ℝ) with hc | hc
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_92 y (by linarith) (by linarith)
                have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
                have hw3 : (1181561/10000000000000:ℝ) ≤ wfun (x + y) := wc_242 (x + y) (by linarith) (by linarith)
                have hw4 : (3586667/1250000000000:ℝ) ≤ wfun (y + z) := wc_229 (y + z) (by linarith) (by linarith)
                have hw5 : (12788137/156250000000:ℝ) ≤ wfun (x + y + z) := wc_560 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_92 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                have hw3 : (1181561/10000000000000:ℝ) ≤ wfun (x + y) := wc_242 (x + y) (by linarith) (by linarith)
                have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_231 (y + z) (by linarith) (by linarith)
                have hw5 : (56830383/625000000000:ℝ) ≤ wfun (x + y + z) := wc_571 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total z (1063/1024:ℝ) with hc | hc
        · rcases le_total x (2151/2048:ℝ) with hc | hc
          · rcases le_total y (4047/2048:ℝ) with hc | hc
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_95 y (by linarith) (by linarith)
              have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
              have hw3 : (1181561/10000000000000:ℝ) ≤ wfun (x + y) := wc_242 (x + y) (by linarith) (by linarith)
              have hw4 : (3586667/1250000000000:ℝ) ≤ wfun (y + z) := wc_227 (y + z) (by linarith) (by linarith)
              have hw5 : (648981217/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_543 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_99 y (by linarith) (by linarith)
              have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
              have hw3 : (2076333/2000000000000:ℝ) ≤ wfun (x + y) := wc_256 (x + y) (by linarith) (by linarith)
              have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_230 (y + z) (by linarith) (by linarith)
              have hw5 : (730420113/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_558 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (4047/2048:ℝ) with hc | hc
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_95 y (by linarith) (by linarith)
              have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
              have hw3 : (2076333/2000000000000:ℝ) ≤ wfun (x + y) := wc_256 (x + y) (by linarith) (by linarith)
              have hw4 : (3586667/1250000000000:ℝ) ≤ wfun (y + z) := wc_227 (y + z) (by linarith) (by linarith)
              have hw5 : (730420113/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_558 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_99 y (by linarith) (by linarith)
              have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
              have hw3 : (14329561/5000000000000:ℝ) ≤ wfun (x + y) := wc_270 (x + y) (by linarith) (by linarith)
              have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_230 (y + z) (by linarith) (by linarith)
              have hw5 : (25514763/312500000000:ℝ) ≤ wfun (x + y + z) := wc_561 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (2151/2048:ℝ) with hc | hc
          · rcases le_total y (4047/2048:ℝ) with hc | hc
            · rcases le_total z (2131/2048:ℝ) with hc | hc
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_95 y (by linarith) (by linarith)
                have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
                have hw3 : (1181561/10000000000000:ℝ) ≤ wfun (x + y) := wc_242 (x + y) (by linarith) (by linarith)
                have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_231 (y + z) (by linarith) (by linarith)
                have hw5 : (12788137/156250000000:ℝ) ≤ wfun (x + y + z) := wc_560 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total x (4297/4096:ℝ) with hc | hc
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                  have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_95 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                  have hw3 : (29587/250000000000:ℝ) ≤ wfun (x + y) := wc_241 (x + y) (by linarith) (by linarith)
                  have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_234 (y + z) (by linarith) (by linarith)
                  have hw5 : (910381357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_570 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                  have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_95 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                  have hw3 : (465149/1000000000000:ℝ) ≤ wfun (x + y) := wc_251 (x + y) (by linarith) (by linarith)
                  have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_234 (y + z) (by linarith) (by linarith)
                  have hw5 : (191513687/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_577 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total z (2131/2048:ℝ) with hc | hc
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_99 y (by linarith) (by linarith)
                have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
                have hw3 : (2076333/2000000000000:ℝ) ≤ wfun (x + y) := wc_256 (x + y) (by linarith) (by linarith)
                have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_234 (y + z) (by linarith) (by linarith)
                have hw5 : (56830383/625000000000:ℝ) ≤ wfun (x + y + z) := wc_571 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total x (4297/4096:ℝ) with hc | hc
                · rcases le_total y (8099/4096:ℝ) with hc | hc
                  · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                    have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                    have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_254 (x + y) (by linarith) (by linarith)
                    have hw5 : (1007100179/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_579 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                    have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                    have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_262 (x + y) (by linarith) (by linarith)
                    have hw5 : (528304163/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_591 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total y (8099/4096:ℝ) with hc | hc
                  · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                    have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                    have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_262 (x + y) (by linarith) (by linarith)
                    have hw5 : (528304163/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_591 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                    have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                    have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_268 (x + y) (by linarith) (by linarith)
                    have hw5 : (553620607/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_595 (x + y + z) (by linarith) (by linarith)
                    linarith
          · rcases le_total y (4047/2048:ℝ) with hc | hc
            · rcases le_total z (2131/2048:ℝ) with hc | hc
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_95 y (by linarith) (by linarith)
                have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
                have hw3 : (2076333/2000000000000:ℝ) ≤ wfun (x + y) := wc_256 (x + y) (by linarith) (by linarith)
                have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_231 (y + z) (by linarith) (by linarith)
                have hw5 : (56830383/625000000000:ℝ) ≤ wfun (x + y + z) := wc_571 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total x (4307/4096:ℝ) with hc | hc
                · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                  have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_95 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                  have hw3 : (649907/625000000000:ℝ) ≤ wfun (x + y) := wc_255 (x + y) (by linarith) (by linarith)
                  have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_234 (y + z) (by linarith) (by linarith)
                  have hw5 : (1005888959/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_580 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                  have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_95 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                  have hw3 : (736743/400000000000:ℝ) ≤ wfun (x + y) := wc_263 (x + y) (by linarith) (by linarith)
                  have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_234 (y + z) (by linarith) (by linarith)
                  have hw5 : (1055337947/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_592 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total z (2131/2048:ℝ) with hc | hc
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_99 y (by linarith) (by linarith)
                have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
                have hw3 : (14329561/5000000000000:ℝ) ≤ wfun (x + y) := wc_270 (x + y) (by linarith) (by linarith)
                have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_234 (y + z) (by linarith) (by linarith)
                have hw5 : (1004679561/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_581 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total x (4307/4096:ℝ) with hc | hc
                · rcases le_total y (8099/4096:ℝ) with hc | hc
                  · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                    have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                    have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_268 (x + y) (by linarith) (by linarith)
                    have hw5 : (553620607/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_595 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                    have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                    have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_278 (x + y) (by linarith) (by linarith)
                    have hw5 : (1158993733/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_603 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total y (8099/4096:ℝ) with hc | hc
                  · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                    have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                    have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_278 (x + y) (by linarith) (by linarith)
                    have hw5 : (1158993733/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_603 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                    have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                    have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_284 (x + y) (by linarith) (by linarith)
                    have hw5 : (242372143/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_608 (x + y + z) (by linarith) (by linarith)
                    linarith

set_option maxHeartbeats 20000000 in
lemma ch_65 (x y z : ℝ) (hx1 : (17/16:ℝ) ≤ x) (hx2 : x ≤ (73/64:ℝ))
    (hy1 : (747/256:ℝ) ≤ y) (hy2 : y ≤ (389/128:ℝ))
    (hz1 : (63/64:ℝ) ≤ z) (hz2 : z ≤ (73/64:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
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
        · have hw0 : (44604923/2500000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
          have hw1 : (261299809/2000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
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
          · rcases le_total x (277/256:ℝ) with hc | hc
            · rcases le_total z (267/256:ℝ) with hc | hc
              · have hw0 : (38452957/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (100676353/250000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_13 z (by linarith) (by linarith)
                have hw4 : (122092393/5000000000000:ℝ) ≤ wfun (y + z) := wc_407 (y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total y (6007/2048:ℝ) with hc | hc
                · have hw0 : (38452957/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                  have hw1 : (2995265257/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
                  have hw3 : (4221/10000000000000:ℝ) ≤ wfun (x + y) := by
                    rcases le_total (x + y) (4:ℝ) with hq30 | hq30
                    · exact le_trans (by norm_num) (wc_420 (x + y) (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_443 (x + y) (by linarith) (by linarith))
                  have hw4 : (82600037/5000000000000:ℝ) ≤ wfun (y + z) := wc_411 (y + z) (by linarith) (by linarith)
                  have hw5 : (33101423/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_774 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (38452957/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                  have hw1 : (816631931/2000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                  have hw4 : (436723/500000000000:ℝ) ≤ wfun (y + z) := by
                    rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                    · exact le_trans (by norm_num) (wc_417 (y + z) (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_439 (y + z) (by linarith) (by linarith))
                  have hw5 : (181069953/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_801 (x + y + z) (by linarith) (by linarith)
                  linarith
            · have hw0 : (4137262453/10000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (100676353/250000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
              have hw4 : (436723/500000000000:ℝ) ≤ wfun (y + z) := by
                rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                · exact le_trans (by norm_num) (wc_408 (y + z) (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_439 (y + z) (by linarith) (by linarith))
              have hw5 : (32210921/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_775 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (277/256:ℝ) with hc | hc
            · rcases le_total z (267/256:ℝ) with hc | hc
              · rcases le_total y (6069/2048:ℝ) with hc | hc
                · have hw0 : (38452957/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                  have hw1 : (2539642107/10000000000000:ℝ) ≤ wfun y := wc_195 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_13 z (by linarith) (by linarith)
                  have hw4 : (34242453/10000000000000:ℝ) ≤ wfun (y + z) := by
                    rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                    · exact le_trans (by norm_num) (wc_416 (y + z) (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_436 (y + z) (by linarith) (by linarith))
                  have hw5 : (31511369/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_797 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total x (549/512:ℝ) with hc | hc
                  · rcases le_total z (529/512:ℝ) with hc | hc
                    · have hw0 : (9984781/500000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                      have hw1 : (1362675081/10000000000000:ℝ) ≤ wfun y := wc_204 y (by linarith) (by linarith)
                      have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
                      have hw3 : (9485773/2000000000000:ℝ) ≤ wfun (x + y) := wc_494 (x + y) (by linarith) (by linarith)
                      have hw4 : (2673983/5000000000000:ℝ) ≤ wfun (y + z) := by
                        rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                        · exact le_trans (by norm_num) (wc_426 (y + z) (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_441 (y + z) (by linarith) (by linarith))
                      have hw5 : (1130887/31250000000:ℝ) ≤ wfun (x + y + z) := wc_850 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (9984781/500000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                      have hw1 : (1362675081/10000000000000:ℝ) ≤ wfun y := wc_204 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
                      have hw3 : (9485773/2000000000000:ℝ) ≤ wfun (x + y) := wc_494 (x + y) (by linarith) (by linarith)
                      have hw5 : (57364627/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_889 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (1609622259/10000000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                    have hw1 : (1362675081/10000000000000:ℝ) ≤ wfun y := wc_204 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_13 z (by linarith) (by linarith)
                    have hw3 : (86688141/5000000000000:ℝ) ≤ wfun (x + y) := wc_515 (x + y) (by linarith) (by linarith)
                    have hw5 : (569259631/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_890 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total y (6069/2048:ℝ) with hc | hc
                · rcases le_total x (549/512:ℝ) with hc | hc
                  · rcases le_total z (539/512:ℝ) with hc | hc
                    · rcases le_total y (12107/4096:ℝ) with hc | hc
                      · have hw0 : (9984781/500000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                        have hw1 : (3285883949/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
                        have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                        have hw4 : (9692591/5000000000000:ℝ) ≤ wfun (y + z) := by
                          rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                          · exact le_trans (by norm_num) (wc_428 (y + z) (by linarith) (by linarith))
                          exact le_trans (by norm_num) (wc_437 (y + z) (by linarith) (by linarith))
                        have hw5 : (227036969/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_862 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (9984781/500000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                        have hw1 : (319327517/1250000000000:ℝ) ≤ wfun y := wc_200 y (by linarith) (by linarith)
                        have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                        have hw3 : (2002543/5000000000000:ℝ) ≤ wfun (x + y) := wc_469 (x + y) (by linarith) (by linarith)
                        have hw5 : (63145721/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_897 (x + y + z) (by linarith) (by linarith)
                        linarith
                    · have hw0 : (9984781/500000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                      have hw1 : (2539642107/10000000000000:ℝ) ≤ wfun y := wc_195 y (by linarith) (by linarith)
                      have hw5 : (342044549/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_904 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (1609622259/10000000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                    have hw1 : (2539642107/10000000000000:ℝ) ≤ wfun y := wc_195 y (by linarith) (by linarith)
                    have hw3 : (11672323/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
                    have hw5 : (339431207/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_905 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total x (549/512:ℝ) with hc | hc
                  · rcases le_total z (539/512:ℝ) with hc | hc
                    · have hw0 : (9984781/500000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                      have hw1 : (1362675081/10000000000000:ℝ) ≤ wfun y := wc_204 y (by linarith) (by linarith)
                      have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                      have hw3 : (9485773/2000000000000:ℝ) ≤ wfun (x + y) := wc_494 (x + y) (by linarith) (by linarith)
                      have hw5 : (831578409/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_927 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (9984781/500000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                      have hw1 : (1362675081/10000000000000:ℝ) ≤ wfun y := wc_204 y (by linarith) (by linarith)
                      have hw3 : (9485773/2000000000000:ℝ) ≤ wfun (x + y) := wc_494 (x + y) (by linarith) (by linarith)
                      have hw4 : (32421/1000000000000:ℝ) ≤ wfun (y + z) := wc_464 (y + z) (by linarith) (by linarith)
                      have hw5 : (1134166649/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_952 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (1609622259/10000000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                    have hw1 : (1362675081/10000000000000:ℝ) ≤ wfun y := wc_204 y (by linarith) (by linarith)
                    have hw3 : (86688141/5000000000000:ℝ) ≤ wfun (x + y) := wc_515 (x + y) (by linarith) (by linarith)
                    have hw5 : (1125526841/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_953 (x + y + z) (by linarith) (by linarith)
                    linarith
            · have hw0 : (4137262453/10000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (67339097/500000000000:ℝ) ≤ wfun y := wc_196 y (by linarith) (by linarith)
              have hw3 : (92147329/10000000000000:ℝ) ≤ wfun (x + y) := wc_501 (x + y) (by linarith) (by linarith)
              have hw5 : (432607663/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_864 (x + y + z) (by linarith) (by linarith)
              linarith
      · have hw0 : (11778340313/10000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
        have hw1 : (261299809/2000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
        have hw3 : (1440757/2000000000000:ℝ) ≤ wfun (x + y) := wc_473 (x + y) (by linarith) (by linarith)
        linarith
    · rcases le_total x (141/128:ℝ) with hc | hc
      · rcases le_total z (131/128:ℝ) with hc | hc
        · have hw0 : (44604923/2500000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
          have hw2 : (2370342229/2500000000000:ℝ) ≤ wfun z := by
            rcases le_total z (1:ℝ) with hq20 | hq20
            · exact le_trans (by norm_num) (wc_5 z (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_7 z (by linarith) (by linarith))
          have hw3 : (64064721/2500000000000:ℝ) ≤ wfun (x + y) := wc_524 (x + y) (by linarith) (by linarith)
          have hw5 : (42660549/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_782 (x + y + z) (by linarith) (by linarith)
          linarith
        · rcases le_total y (3081/1024:ℝ) with hc | hc
          · rcases le_total x (277/256:ℝ) with hc | hc
            · rcases le_total z (267/256:ℝ) with hc | hc
              · have hw0 : (38452957/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (102076243/10000000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (3:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_212 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_220 y (by linarith) (by linarith))
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_13 z (by linarith) (by linarith)
                have hw3 : (134503623/5000000000000:ℝ) ≤ wfun (x + y) := wc_522 (x + y) (by linarith) (by linarith)
                have hw5 : (345435191/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_910 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (38452957/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (102076243/10000000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (3:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_212 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_220 y (by linarith) (by linarith))
                have hw3 : (134503623/5000000000000:ℝ) ≤ wfun (x + y) := wc_522 (x + y) (by linarith) (by linarith)
                have hw4 : (999363/625000000000:ℝ) ≤ wfun (y + z) := wc_483 (y + z) (by linarith) (by linarith)
                have hw5 : (641911203/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_959 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (4137262453/10000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (102076243/10000000000000:ℝ) ≤ wfun y := by
                rcases le_total y (3:ℝ) with hq10 | hq10
                · exact le_trans (by norm_num) (wc_212 y (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_220 y (by linarith) (by linarith))
              have hw3 : (32774279/400000000000:ℝ) ≤ wfun (x + y) := wc_566 (x + y) (by linarith) (by linarith)
              have hw5 : (252901217/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_960 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (44604923/2500000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
            have hw3 : (1219525351/10000000000000:ℝ) ≤ wfun (x + y) := wc_625 (x + y) (by linarith) (by linarith)
            have hw4 : (7204521/625000000000:ℝ) ≤ wfun (y + z) := wc_505 (y + z) (by linarith) (by linarith)
            have hw5 : (815292227/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_965 (x + y + z) (by linarith) (by linarith)
            linarith
      · have hw0 : (11778340313/10000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
        have hw3 : (1572805651/10000000000000:ℝ) ≤ wfun (x + y) := wc_695 (x + y) (by linarith) (by linarith)
        have hw5 : (635374807/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_913 (x + y + z) (by linarith) (by linarith)
        linarith
  · rcases le_total y (1525/512:ℝ) with hc | hc
    · rcases le_total x (141/128:ℝ) with hc | hc
      · rcases le_total z (141/128:ℝ) with hc | hc
        · rcases le_total y (3019/1024:ℝ) with hc | hc
          · have hw0 : (44604923/2500000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
            have hw1 : (100676353/250000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
            have hw2 : (44604923/2500000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
            have hw5 : (14726831/625000000000:ℝ) ≤ wfun (x + y + z) := wc_822 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (44604923/2500000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
            have hw1 : (67339097/500000000000:ℝ) ≤ wfun y := wc_196 y (by linarith) (by linarith)
            have hw2 : (44604923/2500000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
            have hw5 : (908599599/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_938 (x + y + z) (by linarith) (by linarith)
            linarith
        · have hw0 : (44604923/2500000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
          have hw1 : (261299809/2000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
          have hw2 : (11778340313/10000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
          have hw4 : (1440757/2000000000000:ℝ) ≤ wfun (y + z) := wc_473 (y + z) (by linarith) (by linarith)
          have hw5 : (1153447231/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_956 (x + y + z) (by linarith) (by linarith)
          linarith
      · have hw0 : (11778340313/10000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
        have hw1 : (261299809/2000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
        have hw2 : (15429929/1000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
        have hw3 : (1440757/2000000000000:ℝ) ≤ wfun (x + y) := wc_473 (x + y) (by linarith) (by linarith)
        have hw5 : (563934301/5000000000000:ℝ) ≤ wfun (x + y + z) := by
          rcases le_total (x + y + z) (21/4:ℝ) with hq50 | hq50
          · exact le_trans (by norm_num) (wc_957 (x + y + z) (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_971 (x + y + z) (by linarith) (by linarith))
        linarith
    · have hw0 : (15429929/1000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
      have hw2 : (15429929/1000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
      have hw3 : (246785359/10000000000000:ℝ) ≤ wfun (x + y) := wc_525 (x + y) (by linarith) (by linarith)
      have hw4 : (246785359/10000000000000:ℝ) ≤ wfun (y + z) := wc_525 (y + z) (by linarith) (by linarith)
      have hw5 : (96139667/500000000000:ℝ) ≤ wfun (x + y + z) := by
        rcases le_total (x + y + z) (21/4:ℝ) with hq50 | hq50
        · exact le_trans (by norm_num) (wc_967 (x + y + z) (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_975 (x + y + z) (by linarith) (by linarith))
      linarith

set_option maxHeartbeats 20000000 in
lemma ch_68 (x y z : ℝ) (hx1 : (63/64:ℝ) ≤ x) (hx2 : x ≤ (73/64:ℝ))
    (hy1 : (237/64:ℝ) ≤ y) (hy2 : y ≤ (231/40:ℝ))
    (hz1 : (63/64:ℝ) ≤ z) (hz2 : z ≤ (73/64:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total y (3033/640:ℝ) with hc | hc
  · rcases le_total y (5403/1280:ℝ) with hc | hc
    · rcases le_total y (10143/2560:ℝ) with hc | hc
      · have hw1 : (957611737/10000000000000:ℝ) ≤ wfun y := by
          rcases le_total y (15/4:ℝ) with hq10 | hq10
          · exact le_trans (by norm_num) (wc_402 y (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_403 y (by linarith) (by linarith))
        linarith
      · linarith
    · linarith
  · linarith

set_option maxHeartbeats 20000000 in
lemma ch_70 (x y z : ℝ) (hx1 : (63/32:ℝ) ≤ x) (hx2 : x ≤ (131/64:ℝ))
    (hy1 : (63/64:ℝ) ≤ y) (hy2 : y ≤ (17/16:ℝ))
    (hz1 : (121/64:ℝ) ≤ z) (hz2 : z ≤ (131/64:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total z (63/32:ℝ) with hc | hc
  · have hw2 : (795663039/1250000000000:ℝ) ≤ wfun z := wc_76 z (by linarith) (by linarith)
    linarith
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
        linarith
      · rcases le_total z (257/128:ℝ) with hc | hc
        · rcases le_total x (509/256:ℝ) with hc | hc
          · rcases le_total y (267/256:ℝ) with hc | hc
            · have hw0 : (396477691/1250000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
              have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_13 y (by linarith) (by linarith)
              have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                rcases le_total z (2:ℝ) with hq20 | hq20
                · exact le_trans (by norm_num) (wc_90 z (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
              linarith
            · rcases le_total z (509/256:ℝ) with hc | hc
              · have hw0 : (396477691/1250000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
                have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
                linarith
              · rcases le_total x (1013/512:ℝ) with hc | hc
                · have hw0 : (4884069333/10000000000000:ℝ) ≤ wfun x := wc_88 x (by linarith) (by linarith)
                  have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                    rcases le_total z (2:ℝ) with hq20 | hq20
                    · exact le_trans (by norm_num) (wc_130 z (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                  have hw4 : (88186617/10000000000000:ℝ) ≤ wfun (y + z) := wc_306 (y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total y (539/512:ℝ) with hc | hc
                  · rcases le_total z (1023/512:ℝ) with hc | hc
                    · have hw0 : (3192232409/10000000000000:ℝ) ≤ wfun x := wc_105 x (by linarith) (by linarith)
                      have hw1 : (160574441/10000000000000:ℝ) ≤ wfun y := wc_30 y (by linarith) (by linarith)
                      have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_129 z (by linarith) (by linarith)
                      have hw3 : (231767/2000000000000:ℝ) ≤ wfun (x + y) := wc_246 (x + y) (by linarith) (by linarith)
                      have hw4 : (18095851/2000000000000:ℝ) ≤ wfun (y + z) := wc_304 (y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (3192232409/10000000000000:ℝ) ≤ wfun x := wc_105 x (by linarith) (by linarith)
                      have hw1 : (160574441/10000000000000:ℝ) ≤ wfun y := wc_30 y (by linarith) (by linarith)
                      have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                        rcases le_total z (2:ℝ) with hq20 | hq20
                        · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                      have hw3 : (231767/2000000000000:ℝ) ≤ wfun (x + y) := wc_246 (x + y) (by linarith) (by linarith)
                      have hw4 : (63967043/2000000000000:ℝ) ≤ wfun (y + z) := wc_344 (y + z) (by linarith) (by linarith)
                      have hw5 : (449469/312500000000:ℝ) ≤ wfun (x + y + z) := wc_768 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (3192232409/10000000000000:ℝ) ≤ wfun x := wc_105 x (by linarith) (by linarith)
                    have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                      rcases le_total z (2:ℝ) with hq20 | hq20
                      · exact le_trans (by norm_num) (wc_130 z (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                    have hw3 : (18095851/2000000000000:ℝ) ≤ wfun (x + y) := wc_304 (x + y) (by linarith) (by linarith)
                    have hw4 : (157881813/5000000000000:ℝ) ≤ wfun (y + z) := wc_345 (y + z) (by linarith) (by linarith)
                    have hw5 : (3568011/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_769 (x + y + z) (by linarith) (by linarith)
                    linarith
          · rcases le_total y (267/256:ℝ) with hc | hc
            · rcases le_total z (509/256:ℝ) with hc | hc
              · have hw0 : (179073511/2000000000000:ℝ) ≤ wfun x := by
                  rcases le_total x (2:ℝ) with hq00 | hq00
                  · exact le_trans (by norm_num) (wc_130 x (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_141 x (by linarith) (by linarith))
                have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_13 y (by linarith) (by linarith)
                have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
                linarith
              · rcases le_total x (1023/512:ℝ) with hc | hc
                · rcases le_total y (529/512:ℝ) with hc | hc
                  · have hw0 : (1865845891/10000000000000:ℝ) ≤ wfun x := wc_129 x (by linarith) (by linarith)
                    have hw1 : (1175437333/2500000000000:ℝ) ≤ wfun y := wc_12 y (by linarith) (by linarith)
                    have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                      rcases le_total z (2:ℝ) with hq20 | hq20
                      · exact le_trans (by norm_num) (wc_130 z (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                    linarith
                  · rcases le_total z (1023/512:ℝ) with hc | hc
                    · have hw0 : (1865845891/10000000000000:ℝ) ≤ wfun x := wc_129 x (by linarith) (by linarith)
                      have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_17 y (by linarith) (by linarith)
                      have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_129 z (by linarith) (by linarith)
                      have hw3 : (231767/2000000000000:ℝ) ≤ wfun (x + y) := wc_246 (x + y) (by linarith) (by linarith)
                      have hw4 : (231767/2000000000000:ℝ) ≤ wfun (y + z) := wc_246 (y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (1865845891/10000000000000:ℝ) ≤ wfun x := wc_129 x (by linarith) (by linarith)
                      have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_17 y (by linarith) (by linarith)
                      have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                        rcases le_total z (2:ℝ) with hq20 | hq20
                        · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                      have hw3 : (231767/2000000000000:ℝ) ≤ wfun (x + y) := wc_246 (x + y) (by linarith) (by linarith)
                      have hw4 : (18095851/2000000000000:ℝ) ≤ wfun (y + z) := wc_304 (y + z) (by linarith) (by linarith)
                      have hw5 : (449469/312500000000:ℝ) ≤ wfun (x + y + z) := wc_768 (x + y + z) (by linarith) (by linarith)
                      linarith
                · rcases le_total y (529/512:ℝ) with hc | hc
                  · have hw0 : (179073511/2000000000000:ℝ) ≤ wfun x := by
                      rcases le_total x (2:ℝ) with hq00 | hq00
                      · exact le_trans (by norm_num) (wc_138 x (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_141 x (by linarith) (by linarith))
                    have hw1 : (1175437333/2500000000000:ℝ) ≤ wfun y := wc_12 y (by linarith) (by linarith)
                    have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                      rcases le_total z (2:ℝ) with hq20 | hq20
                      · exact le_trans (by norm_num) (wc_130 z (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                    have hw3 : (231767/2000000000000:ℝ) ≤ wfun (x + y) := wc_246 (x + y) (by linarith) (by linarith)
                    linarith
                  · rcases le_total z (1023/512:ℝ) with hc | hc
                    · have hw0 : (179073511/2000000000000:ℝ) ≤ wfun x := by
                        rcases le_total x (2:ℝ) with hq00 | hq00
                        · exact le_trans (by norm_num) (wc_138 x (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_141 x (by linarith) (by linarith))
                      have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_17 y (by linarith) (by linarith)
                      have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_129 z (by linarith) (by linarith)
                      have hw3 : (18095851/2000000000000:ℝ) ≤ wfun (x + y) := wc_304 (x + y) (by linarith) (by linarith)
                      have hw4 : (231767/2000000000000:ℝ) ≤ wfun (y + z) := wc_246 (y + z) (by linarith) (by linarith)
                      have hw5 : (449469/312500000000:ℝ) ≤ wfun (x + y + z) := wc_768 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · rcases le_total x (2051/1024:ℝ) with hc | hc
                      · rcases le_total y (1063/1024:ℝ) with hc | hc
                        · have hw0 : (1337086167/10000000000000:ℝ) ≤ wfun x := by
                            rcases le_total x (2:ℝ) with hq00 | hq00
                            · exact le_trans (by norm_num) (wc_138 x (by linarith) (by linarith))
                            exact le_trans (by norm_num) (wc_140 x (by linarith) (by linarith))
                          have hw1 : (2957142633/10000000000000:ℝ) ≤ wfun y := wc_16 y (by linarith) (by linarith)
                          have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                            rcases le_total z (2:ℝ) with hq20 | hq20
                            · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                            exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                          have hw3 : (11456693/1250000000000:ℝ) ≤ wfun (x + y) := wc_302 (x + y) (by linarith) (by linarith)
                          have hw4 : (91064031/10000000000000:ℝ) ≤ wfun (y + z) := wc_303 (y + z) (by linarith) (by linarith)
                          have hw5 : (314267/40000000000:ℝ) ≤ wfun (x + y + z) := wc_785 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · have hw0 : (1337086167/10000000000000:ℝ) ≤ wfun x := by
                            rcases le_total x (2:ℝ) with hq00 | hq00
                            · exact le_trans (by norm_num) (wc_138 x (by linarith) (by linarith))
                            exact le_trans (by norm_num) (wc_140 x (by linarith) (by linarith))
                          have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_21 y (by linarith) (by linarith)
                          have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                            rcases le_total z (2:ℝ) with hq20 | hq20
                            · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                            exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                          have hw3 : (190300253/10000000000000:ℝ) ≤ wfun (x + y) := wc_328 (x + y) (by linarith) (by linarith)
                          have hw4 : (189078223/10000000000000:ℝ) ≤ wfun (y + z) := wc_329 (y + z) (by linarith) (by linarith)
                          have hw5 : (6477343/500000000000:ℝ) ≤ wfun (x + y + z) := wc_794 (x + y + z) (by linarith) (by linarith)
                          linarith
                      · rcases le_total y (1063/1024:ℝ) with hc | hc
                        · have hw0 : (179073511/2000000000000:ℝ) ≤ wfun x := wc_143 x (by linarith) (by linarith)
                          have hw1 : (2957142633/10000000000000:ℝ) ≤ wfun y := wc_16 y (by linarith) (by linarith)
                          have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                            rcases le_total z (2:ℝ) with hq20 | hq20
                            · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                            exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                          have hw3 : (190300253/10000000000000:ℝ) ≤ wfun (x + y) := wc_328 (x + y) (by linarith) (by linarith)
                          have hw4 : (91064031/10000000000000:ℝ) ≤ wfun (y + z) := wc_303 (y + z) (by linarith) (by linarith)
                          have hw5 : (6477343/500000000000:ℝ) ≤ wfun (x + y + z) := wc_794 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · have hw0 : (179073511/2000000000000:ℝ) ≤ wfun x := wc_143 x (by linarith) (by linarith)
                          have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_21 y (by linarith) (by linarith)
                          have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                            rcases le_total z (2:ℝ) with hq20 | hq20
                            · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                            exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                          have hw3 : (161986357/5000000000000:ℝ) ≤ wfun (x + y) := wc_342 (x + y) (by linarith) (by linarith)
                          have hw4 : (189078223/10000000000000:ℝ) ≤ wfun (y + z) := wc_329 (y + z) (by linarith) (by linarith)
                          have hw5 : (12062377/625000000000:ℝ) ≤ wfun (x + y + z) := wc_805 (x + y + z) (by linarith) (by linarith)
                          linarith
            · rcases le_total z (509/256:ℝ) with hc | hc
              · rcases le_total x (1023/512:ℝ) with hc | hc
                · have hw0 : (1865845891/10000000000000:ℝ) ≤ wfun x := wc_129 x (by linarith) (by linarith)
                  have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
                  have hw3 : (22330933/2500000000000:ℝ) ≤ wfun (x + y) := wc_305 (x + y) (by linarith) (by linarith)
                  linarith
                · rcases le_total y (539/512:ℝ) with hc | hc
                  · have hw0 : (179073511/2000000000000:ℝ) ≤ wfun x := by
                      rcases le_total x (2:ℝ) with hq00 | hq00
                      · exact le_trans (by norm_num) (wc_138 x (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_141 x (by linarith) (by linarith))
                    have hw1 : (160574441/10000000000000:ℝ) ≤ wfun y := wc_30 y (by linarith) (by linarith)
                    have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
                    have hw3 : (63967043/2000000000000:ℝ) ≤ wfun (x + y) := wc_344 (x + y) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (179073511/2000000000000:ℝ) ≤ wfun x := by
                      rcases le_total x (2:ℝ) with hq00 | hq00
                      · exact le_trans (by norm_num) (wc_138 x (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_141 x (by linarith) (by linarith))
                    have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
                    have hw3 : (685641829/10000000000000:ℝ) ≤ wfun (x + y) := wc_356 (x + y) (by linarith) (by linarith)
                    have hw4 : (285997/2500000000000:ℝ) ≤ wfun (y + z) := wc_247 (y + z) (by linarith) (by linarith)
                    have hw5 : (3568011/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_769 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total x (1023/512:ℝ) with hc | hc
                · rcases le_total y (539/512:ℝ) with hc | hc
                  · rcases le_total z (1023/512:ℝ) with hc | hc
                    · rcases le_total x (2041/1024:ℝ) with hc | hc
                      · have hw0 : (248869577/1000000000000:ℝ) ≤ wfun x := wc_128 x (by linarith) (by linarith)
                        have hw1 : (160574441/10000000000000:ℝ) ≤ wfun y := wc_30 y (by linarith) (by linarith)
                        have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_129 z (by linarith) (by linarith)
                        have hw3 : (91064031/10000000000000:ℝ) ≤ wfun (x + y) := wc_303 (x + y) (by linarith) (by linarith)
                        have hw4 : (18095851/2000000000000:ℝ) ≤ wfun (y + z) := wc_304 (y + z) (by linarith) (by linarith)
                        have hw5 : (2887779/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_767 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · rcases le_total y (1073/1024:ℝ) with hc | hc
                        · have hw0 : (1867963109/10000000000000:ℝ) ≤ wfun x := wc_136 x (by linarith) (by linarith)
                          have hw1 : (349265369/5000000000000:ℝ) ≤ wfun y := wc_29 y (by linarith) (by linarith)
                          have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_129 z (by linarith) (by linarith)
                          have hw3 : (190300253/10000000000000:ℝ) ≤ wfun (x + y) := wc_328 (x + y) (by linarith) (by linarith)
                          have hw4 : (91064031/10000000000000:ℝ) ≤ wfun (y + z) := wc_303 (y + z) (by linarith) (by linarith)
                          have hw5 : (10044841/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_776 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · have hw0 : (1867963109/10000000000000:ℝ) ≤ wfun x := wc_136 x (by linarith) (by linarith)
                          have hw1 : (160574441/10000000000000:ℝ) ≤ wfun y := wc_45 y (by linarith) (by linarith)
                          have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_129 z (by linarith) (by linarith)
                          have hw3 : (161986357/5000000000000:ℝ) ≤ wfun (x + y) := wc_342 (x + y) (by linarith) (by linarith)
                          have hw4 : (189078223/10000000000000:ℝ) ≤ wfun (y + z) := wc_329 (y + z) (by linarith) (by linarith)
                          have hw5 : (314267/40000000000:ℝ) ≤ wfun (x + y + z) := wc_785 (x + y + z) (by linarith) (by linarith)
                          linarith
                    · rcases le_total x (2041/1024:ℝ) with hc | hc
                      · rcases le_total y (1073/1024:ℝ) with hc | hc
                        · have hw0 : (248869577/1000000000000:ℝ) ≤ wfun x := wc_128 x (by linarith) (by linarith)
                          have hw1 : (349265369/5000000000000:ℝ) ≤ wfun y := wc_29 y (by linarith) (by linarith)
                          have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                            rcases le_total z (2:ℝ) with hq20 | hq20
                            · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                            exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                          have hw3 : (11456693/1250000000000:ℝ) ≤ wfun (x + y) := wc_302 (x + y) (by linarith) (by linarith)
                          have hw4 : (160947823/5000000000000:ℝ) ≤ wfun (y + z) := wc_343 (y + z) (by linarith) (by linarith)
                          have hw5 : (314267/40000000000:ℝ) ≤ wfun (x + y + z) := wc_785 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · have hw0 : (248869577/1000000000000:ℝ) ≤ wfun x := wc_128 x (by linarith) (by linarith)
                          have hw1 : (160574441/10000000000000:ℝ) ≤ wfun y := wc_45 y (by linarith) (by linarith)
                          have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                            rcases le_total z (2:ℝ) with hq20 | hq20
                            · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                            exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                          have hw3 : (190300253/10000000000000:ℝ) ≤ wfun (x + y) := wc_328 (x + y) (by linarith) (by linarith)
                          have hw4 : (489049523/10000000000000:ℝ) ≤ wfun (y + z) := wc_351 (y + z) (by linarith) (by linarith)
                          have hw5 : (6477343/500000000000:ℝ) ≤ wfun (x + y + z) := wc_794 (x + y + z) (by linarith) (by linarith)
                          linarith
                      · rcases le_total y (1073/1024:ℝ) with hc | hc
                        · have hw0 : (1867963109/10000000000000:ℝ) ≤ wfun x := wc_136 x (by linarith) (by linarith)
                          have hw1 : (349265369/5000000000000:ℝ) ≤ wfun y := wc_29 y (by linarith) (by linarith)
                          have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                            rcases le_total z (2:ℝ) with hq20 | hq20
                            · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                            exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                          have hw3 : (190300253/10000000000000:ℝ) ≤ wfun (x + y) := wc_328 (x + y) (by linarith) (by linarith)
                          have hw4 : (160947823/5000000000000:ℝ) ≤ wfun (y + z) := wc_343 (y + z) (by linarith) (by linarith)
                          have hw5 : (6477343/500000000000:ℝ) ≤ wfun (x + y + z) := wc_794 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · have hw0 : (1867963109/10000000000000:ℝ) ≤ wfun x := wc_136 x (by linarith) (by linarith)
                          have hw1 : (160574441/10000000000000:ℝ) ≤ wfun y := wc_45 y (by linarith) (by linarith)
                          have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                            rcases le_total z (2:ℝ) with hq20 | hq20
                            · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                            exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                          have hw3 : (161986357/5000000000000:ℝ) ≤ wfun (x + y) := wc_342 (x + y) (by linarith) (by linarith)
                          have hw4 : (489049523/10000000000000:ℝ) ≤ wfun (y + z) := wc_351 (y + z) (by linarith) (by linarith)
                          have hw5 : (12062377/625000000000:ℝ) ≤ wfun (x + y + z) := wc_805 (x + y + z) (by linarith) (by linarith)
                          linarith
                  · rcases le_total z (1023/512:ℝ) with hc | hc
                    · have hw0 : (1865845891/10000000000000:ℝ) ≤ wfun x := wc_129 x (by linarith) (by linarith)
                      have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_129 z (by linarith) (by linarith)
                      have hw3 : (63967043/2000000000000:ℝ) ≤ wfun (x + y) := wc_344 (x + y) (by linarith) (by linarith)
                      have hw4 : (63967043/2000000000000:ℝ) ≤ wfun (y + z) := wc_344 (y + z) (by linarith) (by linarith)
                      have hw5 : (38980307/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_787 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (1865845891/10000000000000:ℝ) ≤ wfun x := wc_129 x (by linarith) (by linarith)
                      have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                        rcases le_total z (2:ℝ) with hq20 | hq20
                        · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                      have hw3 : (63967043/2000000000000:ℝ) ≤ wfun (x + y) := wc_344 (x + y) (by linarith) (by linarith)
                      have hw4 : (685641829/10000000000000:ℝ) ≤ wfun (y + z) := wc_356 (y + z) (by linarith) (by linarith)
                      have hw5 : (191511939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_807 (x + y + z) (by linarith) (by linarith)
                      linarith
                · rcases le_total y (539/512:ℝ) with hc | hc
                  · rcases le_total z (1023/512:ℝ) with hc | hc
                    · rcases le_total x (2051/1024:ℝ) with hc | hc
                      · rcases le_total y (1073/1024:ℝ) with hc | hc
                        · have hw0 : (1337086167/10000000000000:ℝ) ≤ wfun x := by
                            rcases le_total x (2:ℝ) with hq00 | hq00
                            · exact le_trans (by norm_num) (wc_138 x (by linarith) (by linarith))
                            exact le_trans (by norm_num) (wc_140 x (by linarith) (by linarith))
                          have hw1 : (349265369/5000000000000:ℝ) ≤ wfun y := wc_29 y (by linarith) (by linarith)
                          have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_129 z (by linarith) (by linarith)
                          have hw3 : (161986357/5000000000000:ℝ) ≤ wfun (x + y) := wc_342 (x + y) (by linarith) (by linarith)
                          have hw4 : (91064031/10000000000000:ℝ) ≤ wfun (y + z) := wc_303 (y + z) (by linarith) (by linarith)
                          have hw5 : (314267/40000000000:ℝ) ≤ wfun (x + y + z) := wc_785 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · have hw0 : (1337086167/10000000000000:ℝ) ≤ wfun x := by
                            rcases le_total x (2:ℝ) with hq00 | hq00
                            · exact le_trans (by norm_num) (wc_138 x (by linarith) (by linarith))
                            exact le_trans (by norm_num) (wc_140 x (by linarith) (by linarith))
                          have hw1 : (160574441/10000000000000:ℝ) ≤ wfun y := wc_45 y (by linarith) (by linarith)
                          have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_129 z (by linarith) (by linarith)
                          have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_350 (x + y) (by linarith) (by linarith)
                          have hw4 : (189078223/10000000000000:ℝ) ≤ wfun (y + z) := wc_329 (y + z) (by linarith) (by linarith)
                          have hw5 : (6477343/500000000000:ℝ) ≤ wfun (x + y + z) := wc_794 (x + y + z) (by linarith) (by linarith)
                          linarith
                      · rcases le_total y (1073/1024:ℝ) with hc | hc
                        · have hw0 : (179073511/2000000000000:ℝ) ≤ wfun x := wc_143 x (by linarith) (by linarith)
                          have hw1 : (349265369/5000000000000:ℝ) ≤ wfun y := wc_29 y (by linarith) (by linarith)
                          have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_129 z (by linarith) (by linarith)
                          have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_350 (x + y) (by linarith) (by linarith)
                          have hw4 : (91064031/10000000000000:ℝ) ≤ wfun (y + z) := wc_303 (y + z) (by linarith) (by linarith)
                          have hw5 : (6477343/500000000000:ℝ) ≤ wfun (x + y + z) := wc_794 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · have hw0 : (179073511/2000000000000:ℝ) ≤ wfun x := wc_143 x (by linarith) (by linarith)
                          have hw1 : (160574441/10000000000000:ℝ) ≤ wfun y := wc_45 y (by linarith) (by linarith)
                          have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_129 z (by linarith) (by linarith)
                          have hw3 : (694482783/10000000000000:ℝ) ≤ wfun (x + y) := wc_354 (x + y) (by linarith) (by linarith)
                          have hw4 : (189078223/10000000000000:ℝ) ≤ wfun (y + z) := wc_329 (y + z) (by linarith) (by linarith)
                          have hw5 : (12062377/625000000000:ℝ) ≤ wfun (x + y + z) := wc_805 (x + y + z) (by linarith) (by linarith)
                          linarith
                    · rcases le_total x (2051/1024:ℝ) with hc | hc
                      · rcases le_total y (1073/1024:ℝ) with hc | hc
                        · have hw0 : (1337086167/10000000000000:ℝ) ≤ wfun x := by
                            rcases le_total x (2:ℝ) with hq00 | hq00
                            · exact le_trans (by norm_num) (wc_138 x (by linarith) (by linarith))
                            exact le_trans (by norm_num) (wc_140 x (by linarith) (by linarith))
                          have hw1 : (349265369/5000000000000:ℝ) ≤ wfun y := wc_29 y (by linarith) (by linarith)
                          have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                            rcases le_total z (2:ℝ) with hq20 | hq20
                            · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                            exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                          have hw3 : (161986357/5000000000000:ℝ) ≤ wfun (x + y) := wc_342 (x + y) (by linarith) (by linarith)
                          have hw4 : (160947823/5000000000000:ℝ) ≤ wfun (y + z) := wc_343 (y + z) (by linarith) (by linarith)
                          have hw5 : (12062377/625000000000:ℝ) ≤ wfun (x + y + z) := wc_805 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · have hw0 : (1337086167/10000000000000:ℝ) ≤ wfun x := by
                            rcases le_total x (2:ℝ) with hq00 | hq00
                            · exact le_trans (by norm_num) (wc_138 x (by linarith) (by linarith))
                            exact le_trans (by norm_num) (wc_140 x (by linarith) (by linarith))
                          have hw1 : (160574441/10000000000000:ℝ) ≤ wfun y := wc_45 y (by linarith) (by linarith)
                          have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                            rcases le_total z (2:ℝ) with hq20 | hq20
                            · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                            exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                          have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_350 (x + y) (by linarith) (by linarith)
                          have hw4 : (489049523/10000000000000:ℝ) ≤ wfun (y + z) := wc_351 (y + z) (by linarith) (by linarith)
                          have hw5 : (53757489/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_828 (x + y + z) (by linarith) (by linarith)
                          linarith
                      · rcases le_total y (1073/1024:ℝ) with hc | hc
                        · have hw0 : (179073511/2000000000000:ℝ) ≤ wfun x := wc_143 x (by linarith) (by linarith)
                          have hw1 : (349265369/5000000000000:ℝ) ≤ wfun y := wc_29 y (by linarith) (by linarith)
                          have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                            rcases le_total z (2:ℝ) with hq20 | hq20
                            · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                            exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                          have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_350 (x + y) (by linarith) (by linarith)
                          have hw4 : (160947823/5000000000000:ℝ) ≤ wfun (y + z) := wc_343 (y + z) (by linarith) (by linarith)
                          have hw5 : (53757489/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_828 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · have hw0 : (179073511/2000000000000:ℝ) ≤ wfun x := wc_143 x (by linarith) (by linarith)
                          have hw1 : (160574441/10000000000000:ℝ) ≤ wfun y := wc_45 y (by linarith) (by linarith)
                          have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                            rcases le_total z (2:ℝ) with hq20 | hq20
                            · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                            exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                          have hw3 : (694482783/10000000000000:ℝ) ≤ wfun (x + y) := wc_354 (x + y) (by linarith) (by linarith)
                          have hw4 : (489049523/10000000000000:ℝ) ≤ wfun (y + z) := wc_351 (y + z) (by linarith) (by linarith)
                          have hw5 : (356771293/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_842 (x + y + z) (by linarith) (by linarith)
                          linarith
                  · rcases le_total z (1023/512:ℝ) with hc | hc
                    · have hw0 : (179073511/2000000000000:ℝ) ≤ wfun x := by
                        rcases le_total x (2:ℝ) with hq00 | hq00
                        · exact le_trans (by norm_num) (wc_138 x (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_141 x (by linarith) (by linarith))
                      have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_129 z (by linarith) (by linarith)
                      have hw3 : (685641829/10000000000000:ℝ) ≤ wfun (x + y) := wc_356 (x + y) (by linarith) (by linarith)
                      have hw4 : (63967043/2000000000000:ℝ) ≤ wfun (y + z) := wc_344 (y + z) (by linarith) (by linarith)
                      have hw5 : (191511939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_807 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (179073511/2000000000000:ℝ) ≤ wfun x := by
                        rcases le_total x (2:ℝ) with hq00 | hq00
                        · exact le_trans (by norm_num) (wc_138 x (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_141 x (by linarith) (by linarith))
                      have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                        rcases le_total z (2:ℝ) with hq20 | hq20
                        · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                      have hw3 : (685641829/10000000000000:ℝ) ≤ wfun (x + y) := wc_356 (x + y) (by linarith) (by linarith)
                      have hw4 : (685641829/10000000000000:ℝ) ≤ wfun (y + z) := wc_356 (y + z) (by linarith) (by linarith)
                      have hw5 : (354029429/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_845 (x + y + z) (by linarith) (by linarith)
                      linarith
        · rcases le_total x (509/256:ℝ) with hc | hc
          · rcases le_total y (267/256:ℝ) with hc | hc
            · have hw0 : (396477691/1250000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
              have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_13 y (by linarith) (by linarith)
              have hw4 : (21491553/2500000000000:ℝ) ≤ wfun (y + z) := wc_307 (y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (519/256:ℝ) with hc | hc
              · rcases le_total x (1013/512:ℝ) with hc | hc
                · have hw0 : (4884069333/10000000000000:ℝ) ≤ wfun x := wc_88 x (by linarith) (by linarith)
                  have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_146 z (by linarith) (by linarith)
                  have hw4 : (66837841/1000000000000:ℝ) ≤ wfun (y + z) := wc_358 (y + z) (by linarith) (by linarith)
                  have hw5 : (14162149/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_770 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total y (539/512:ℝ) with hc | hc
                  · have hw0 : (3192232409/10000000000000:ℝ) ≤ wfun x := wc_105 x (by linarith) (by linarith)
                    have hw1 : (160574441/10000000000000:ℝ) ≤ wfun y := wc_30 y (by linarith) (by linarith)
                    have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_146 z (by linarith) (by linarith)
                    have hw3 : (231767/2000000000000:ℝ) ≤ wfun (x + y) := wc_246 (x + y) (by linarith) (by linarith)
                    have hw4 : (676941261/10000000000000:ℝ) ≤ wfun (y + z) := wc_357 (y + z) (by linarith) (by linarith)
                    have hw5 : (38680157/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_788 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (3192232409/10000000000000:ℝ) ≤ wfun x := wc_105 x (by linarith) (by linarith)
                    have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_146 z (by linarith) (by linarith)
                    have hw3 : (18095851/2000000000000:ℝ) ≤ wfun (x + y) := wc_304 (x + y) (by linarith) (by linarith)
                    have hw4 : (1168886057/10000000000000:ℝ) ≤ wfun (y + z) := wc_366 (y + z) (by linarith) (by linarith)
                    have hw5 : (190040129/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_808 (x + y + z) (by linarith) (by linarith)
                    linarith
              · have hw0 : (396477691/1250000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
                have hw4 : (1764735511/10000000000000:ℝ) ≤ wfun (y + z) := wc_370 (y + z) (by linarith) (by linarith)
                have hw5 : (187138697/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_810 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (267/256:ℝ) with hc | hc
            · rcases le_total z (519/256:ℝ) with hc | hc
              · rcases le_total x (1023/512:ℝ) with hc | hc
                · rcases le_total y (529/512:ℝ) with hc | hc
                  · have hw0 : (1865845891/10000000000000:ℝ) ≤ wfun x := wc_129 x (by linarith) (by linarith)
                    have hw1 : (1175437333/2500000000000:ℝ) ≤ wfun y := wc_12 y (by linarith) (by linarith)
                    have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_146 z (by linarith) (by linarith)
                    have hw4 : (22330933/2500000000000:ℝ) ≤ wfun (y + z) := wc_305 (y + z) (by linarith) (by linarith)
                    have hw5 : (3568011/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_769 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · rcases le_total z (1033/512:ℝ) with hc | hc
                    · have hw0 : (1865845891/10000000000000:ℝ) ≤ wfun x := wc_129 x (by linarith) (by linarith)
                      have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_17 y (by linarith) (by linarith)
                      have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_145 z (by linarith) (by linarith)
                      have hw3 : (231767/2000000000000:ℝ) ≤ wfun (x + y) := wc_246 (x + y) (by linarith) (by linarith)
                      have hw4 : (63967043/2000000000000:ℝ) ≤ wfun (y + z) := wc_344 (y + z) (by linarith) (by linarith)
                      have hw5 : (38980307/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_787 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (1865845891/10000000000000:ℝ) ≤ wfun x := wc_129 x (by linarith) (by linarith)
                      have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_17 y (by linarith) (by linarith)
                      have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_149 z (by linarith) (by linarith)
                      have hw3 : (231767/2000000000000:ℝ) ≤ wfun (x + y) := wc_246 (x + y) (by linarith) (by linarith)
                      have hw4 : (685641829/10000000000000:ℝ) ≤ wfun (y + z) := wc_356 (y + z) (by linarith) (by linarith)
                      have hw5 : (191511939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_807 (x + y + z) (by linarith) (by linarith)
                      linarith
                · rcases le_total y (529/512:ℝ) with hc | hc
                  · have hw0 : (179073511/2000000000000:ℝ) ≤ wfun x := by
                      rcases le_total x (2:ℝ) with hq00 | hq00
                      · exact le_trans (by norm_num) (wc_138 x (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_141 x (by linarith) (by linarith))
                    have hw1 : (1175437333/2500000000000:ℝ) ≤ wfun y := wc_12 y (by linarith) (by linarith)
                    have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_146 z (by linarith) (by linarith)
                    have hw3 : (231767/2000000000000:ℝ) ≤ wfun (x + y) := wc_246 (x + y) (by linarith) (by linarith)
                    have hw4 : (22330933/2500000000000:ℝ) ≤ wfun (y + z) := wc_305 (y + z) (by linarith) (by linarith)
                    have hw5 : (38680157/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_788 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · rcases le_total z (1033/512:ℝ) with hc | hc
                    · rcases le_total x (2051/1024:ℝ) with hc | hc
                      · have hw0 : (1337086167/10000000000000:ℝ) ≤ wfun x := by
                          rcases le_total x (2:ℝ) with hq00 | hq00
                          · exact le_trans (by norm_num) (wc_138 x (by linarith) (by linarith))
                          exact le_trans (by norm_num) (wc_140 x (by linarith) (by linarith))
                        have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_17 y (by linarith) (by linarith)
                        have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_145 z (by linarith) (by linarith)
                        have hw3 : (91064031/10000000000000:ℝ) ≤ wfun (x + y) := wc_303 (x + y) (by linarith) (by linarith)
                        have hw4 : (63967043/2000000000000:ℝ) ≤ wfun (y + z) := wc_344 (y + z) (by linarith) (by linarith)
                        have hw5 : (19225319/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_806 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · rcases le_total y (1063/1024:ℝ) with hc | hc
                        · have hw0 : (179073511/2000000000000:ℝ) ≤ wfun x := wc_143 x (by linarith) (by linarith)
                          have hw1 : (2957142633/10000000000000:ℝ) ≤ wfun y := wc_16 y (by linarith) (by linarith)
                          have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_145 z (by linarith) (by linarith)
                          have hw3 : (190300253/10000000000000:ℝ) ≤ wfun (x + y) := wc_328 (x + y) (by linarith) (by linarith)
                          have hw4 : (160947823/5000000000000:ℝ) ≤ wfun (y + z) := wc_343 (y + z) (by linarith) (by linarith)
                          have hw5 : (53757489/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_828 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · have hw0 : (179073511/2000000000000:ℝ) ≤ wfun x := wc_143 x (by linarith) (by linarith)
                          have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_21 y (by linarith) (by linarith)
                          have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_145 z (by linarith) (by linarith)
                          have hw3 : (161986357/5000000000000:ℝ) ≤ wfun (x + y) := wc_342 (x + y) (by linarith) (by linarith)
                          have hw4 : (489049523/10000000000000:ℝ) ≤ wfun (y + z) := wc_351 (y + z) (by linarith) (by linarith)
                          have hw5 : (356771293/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_842 (x + y + z) (by linarith) (by linarith)
                          linarith
                    · have hw0 : (179073511/2000000000000:ℝ) ≤ wfun x := by
                        rcases le_total x (2:ℝ) with hq00 | hq00
                        · exact le_trans (by norm_num) (wc_138 x (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_141 x (by linarith) (by linarith))
                      have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_17 y (by linarith) (by linarith)
                      have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_149 z (by linarith) (by linarith)
                      have hw3 : (18095851/2000000000000:ℝ) ≤ wfun (x + y) := wc_304 (x + y) (by linarith) (by linarith)
                      have hw4 : (685641829/10000000000000:ℝ) ≤ wfun (y + z) := wc_356 (y + z) (by linarith) (by linarith)
                      have hw5 : (354029429/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_845 (x + y + z) (by linarith) (by linarith)
                      linarith
              · rcases le_total x (1023/512:ℝ) with hc | hc
                · have hw0 : (1865845891/10000000000000:ℝ) ≤ wfun x := wc_129 x (by linarith) (by linarith)
                  have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_13 y (by linarith) (by linarith)
                  have hw4 : (66837841/1000000000000:ℝ) ≤ wfun (y + z) := wc_358 (y + z) (by linarith) (by linarith)
                  have hw5 : (37716487/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_809 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (179073511/2000000000000:ℝ) ≤ wfun x := by
                    rcases le_total x (2:ℝ) with hq00 | hq00
                    · exact le_trans (by norm_num) (wc_138 x (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_141 x (by linarith) (by linarith))
                  have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_13 y (by linarith) (by linarith)
                  have hw3 : (285997/2500000000000:ℝ) ≤ wfun (x + y) := wc_247 (x + y) (by linarith) (by linarith)
                  have hw4 : (66837841/1000000000000:ℝ) ≤ wfun (y + z) := wc_358 (y + z) (by linarith) (by linarith)
                  have hw5 : (43578037/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_847 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total z (519/256:ℝ) with hc | hc
              · rcases le_total x (1023/512:ℝ) with hc | hc
                · rcases le_total y (539/512:ℝ) with hc | hc
                  · rcases le_total z (1033/512:ℝ) with hc | hc
                    · rcases le_total x (2041/1024:ℝ) with hc | hc
                      · have hw0 : (248869577/1000000000000:ℝ) ≤ wfun x := wc_128 x (by linarith) (by linarith)
                        have hw1 : (160574441/10000000000000:ℝ) ≤ wfun y := wc_30 y (by linarith) (by linarith)
                        have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_145 z (by linarith) (by linarith)
                        have hw3 : (91064031/10000000000000:ℝ) ≤ wfun (x + y) := wc_303 (x + y) (by linarith) (by linarith)
                        have hw4 : (685641829/10000000000000:ℝ) ≤ wfun (y + z) := wc_356 (y + z) (by linarith) (by linarith)
                        have hw5 : (19225319/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_806 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (1867963109/10000000000000:ℝ) ≤ wfun x := wc_136 x (by linarith) (by linarith)
                        have hw1 : (160574441/10000000000000:ℝ) ≤ wfun y := wc_30 y (by linarith) (by linarith)
                        have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_145 z (by linarith) (by linarith)
                        have hw3 : (189078223/10000000000000:ℝ) ≤ wfun (x + y) := wc_329 (x + y) (by linarith) (by linarith)
                        have hw4 : (685641829/10000000000000:ℝ) ≤ wfun (y + z) := wc_356 (y + z) (by linarith) (by linarith)
                        have hw5 : (26775111/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_830 (x + y + z) (by linarith) (by linarith)
                        linarith
                    · have hw0 : (1865845891/10000000000000:ℝ) ≤ wfun x := wc_129 x (by linarith) (by linarith)
                      have hw1 : (160574441/10000000000000:ℝ) ≤ wfun y := wc_30 y (by linarith) (by linarith)
                      have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_149 z (by linarith) (by linarith)
                      have hw3 : (18095851/2000000000000:ℝ) ≤ wfun (x + y) := wc_304 (x + y) (by linarith) (by linarith)
                      have hw4 : (591930551/5000000000000:ℝ) ≤ wfun (y + z) := wc_365 (y + z) (by linarith) (by linarith)
                      have hw5 : (354029429/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_845 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (1865845891/10000000000000:ℝ) ≤ wfun x := wc_129 x (by linarith) (by linarith)
                    have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_146 z (by linarith) (by linarith)
                    have hw3 : (63967043/2000000000000:ℝ) ≤ wfun (x + y) := wc_344 (x + y) (by linarith) (by linarith)
                    have hw4 : (1168886057/10000000000000:ℝ) ≤ wfun (y + z) := wc_366 (y + z) (by linarith) (by linarith)
                    have hw5 : (43914233/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_846 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total y (539/512:ℝ) with hc | hc
                  · rcases le_total z (1033/512:ℝ) with hc | hc
                    · rcases le_total x (2051/1024:ℝ) with hc | hc
                      · rcases le_total y (1073/1024:ℝ) with hc | hc
                        · have hw0 : (1337086167/10000000000000:ℝ) ≤ wfun x := by
                            rcases le_total x (2:ℝ) with hq00 | hq00
                            · exact le_trans (by norm_num) (wc_138 x (by linarith) (by linarith))
                            exact le_trans (by norm_num) (wc_140 x (by linarith) (by linarith))
                          have hw1 : (349265369/5000000000000:ℝ) ≤ wfun y := wc_29 y (by linarith) (by linarith)
                          have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_145 z (by linarith) (by linarith)
                          have hw3 : (161986357/5000000000000:ℝ) ≤ wfun (x + y) := wc_342 (x + y) (by linarith) (by linarith)
                          have hw4 : (172511147/2500000000000:ℝ) ≤ wfun (y + z) := wc_355 (y + z) (by linarith) (by linarith)
                          have hw5 : (356771293/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_842 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · have hw0 : (1337086167/10000000000000:ℝ) ≤ wfun x := by
                            rcases le_total x (2:ℝ) with hq00 | hq00
                            · exact le_trans (by norm_num) (wc_138 x (by linarith) (by linarith))
                            exact le_trans (by norm_num) (wc_140 x (by linarith) (by linarith))
                          have hw1 : (160574441/10000000000000:ℝ) ≤ wfun y := wc_45 y (by linarith) (by linarith)
                          have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_145 z (by linarith) (by linarith)
                          have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_350 (x + y) (by linarith) (by linarith)
                          have hw4 : (924357731/10000000000000:ℝ) ≤ wfun (y + z) := wc_363 (y + z) (by linarith) (by linarith)
                          have hw5 : (114198739/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_860 (x + y + z) (by linarith) (by linarith)
                          linarith
                      · have hw0 : (179073511/2000000000000:ℝ) ≤ wfun x := wc_143 x (by linarith) (by linarith)
                        have hw1 : (160574441/10000000000000:ℝ) ≤ wfun y := wc_30 y (by linarith) (by linarith)
                        have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_145 z (by linarith) (by linarith)
                        have hw3 : (489049523/10000000000000:ℝ) ≤ wfun (x + y) := wc_351 (x + y) (by linarith) (by linarith)
                        have hw4 : (685641829/10000000000000:ℝ) ≤ wfun (y + z) := wc_356 (y + z) (by linarith) (by linarith)
                        have hw5 : (91007427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_861 (x + y + z) (by linarith) (by linarith)
                        linarith
                    · have hw0 : (179073511/2000000000000:ℝ) ≤ wfun x := by
                        rcases le_total x (2:ℝ) with hq00 | hq00
                        · exact le_trans (by norm_num) (wc_138 x (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_141 x (by linarith) (by linarith))
                      have hw1 : (160574441/10000000000000:ℝ) ≤ wfun y := wc_30 y (by linarith) (by linarith)
                      have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_149 z (by linarith) (by linarith)
                      have hw3 : (63967043/2000000000000:ℝ) ≤ wfun (x + y) := wc_344 (x + y) (by linarith) (by linarith)
                      have hw4 : (591930551/5000000000000:ℝ) ≤ wfun (y + z) := wc_365 (y + z) (by linarith) (by linarith)
                      have hw5 : (112866211/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_880 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (179073511/2000000000000:ℝ) ≤ wfun x := by
                      rcases le_total x (2:ℝ) with hq00 | hq00
                      · exact le_trans (by norm_num) (wc_138 x (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_141 x (by linarith) (by linarith))
                    have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_146 z (by linarith) (by linarith)
                    have hw3 : (685641829/10000000000000:ℝ) ≤ wfun (x + y) := wc_356 (x + y) (by linarith) (by linarith)
                    have hw4 : (1168886057/10000000000000:ℝ) ≤ wfun (y + z) := wc_366 (y + z) (by linarith) (by linarith)
                    have hw5 : (560010683/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_881 (x + y + z) (by linarith) (by linarith)
                    linarith
              · have hw0 : (179073511/2000000000000:ℝ) ≤ wfun x := by
                  rcases le_total x (2:ℝ) with hq00 | hq00
                  · exact le_trans (by norm_num) (wc_130 x (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_141 x (by linarith) (by linarith))
                have hw3 : (88186617/10000000000000:ℝ) ≤ wfun (x + y) := wc_306 (x + y) (by linarith) (by linarith)
                have hw4 : (1764735511/10000000000000:ℝ) ≤ wfun (y + z) := wc_370 (y + z) (by linarith) (by linarith)
                have hw5 : (551493311/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_883 (x + y + z) (by linarith) (by linarith)
                linarith
    · rcases le_total y (131/128:ℝ) with hc | hc
      · have hw1 : (2370342229/2500000000000:ℝ) ≤ wfun y := by
          rcases le_total y (1:ℝ) with hq10 | hq10
          · exact le_trans (by norm_num) (wc_5 y (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_7 y (by linarith) (by linarith))
        linarith
      · rcases le_total z (257/128:ℝ) with hc | hc
        · rcases le_total x (519/256:ℝ) with hc | hc
          · rcases le_total y (267/256:ℝ) with hc | hc
            · rcases le_total z (509/256:ℝ) with hc | hc
              · have hw0 : (13164037/10000000000000:ℝ) ≤ wfun x := wc_146 x (by linarith) (by linarith)
                have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_13 y (by linarith) (by linarith)
                have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
                have hw3 : (88186617/10000000000000:ℝ) ≤ wfun (x + y) := wc_306 (x + y) (by linarith) (by linarith)
                linarith
              · rcases le_total x (1033/512:ℝ) with hc | hc
                · rcases le_total y (529/512:ℝ) with hc | hc
                  · have hw0 : (27945219/1000000000000:ℝ) ≤ wfun x := wc_145 x (by linarith) (by linarith)
                    have hw1 : (1175437333/2500000000000:ℝ) ≤ wfun y := wc_12 y (by linarith) (by linarith)
                    have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                      rcases le_total z (2:ℝ) with hq20 | hq20
                      · exact le_trans (by norm_num) (wc_130 z (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                    have hw3 : (18095851/2000000000000:ℝ) ≤ wfun (x + y) := wc_304 (x + y) (by linarith) (by linarith)
                    have hw5 : (3568011/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_769 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · rcases le_total z (1023/512:ℝ) with hc | hc
                    · have hw0 : (27945219/1000000000000:ℝ) ≤ wfun x := wc_145 x (by linarith) (by linarith)
                      have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_17 y (by linarith) (by linarith)
                      have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_129 z (by linarith) (by linarith)
                      have hw3 : (63967043/2000000000000:ℝ) ≤ wfun (x + y) := wc_344 (x + y) (by linarith) (by linarith)
                      have hw4 : (231767/2000000000000:ℝ) ≤ wfun (y + z) := wc_246 (y + z) (by linarith) (by linarith)
                      have hw5 : (38980307/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_787 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · rcases le_total x (2061/1024:ℝ) with hc | hc
                      · rcases le_total y (1063/1024:ℝ) with hc | hc
                        · have hw0 : (543159341/10000000000000:ℝ) ≤ wfun x := wc_144 x (by linarith) (by linarith)
                          have hw1 : (2957142633/10000000000000:ℝ) ≤ wfun y := wc_16 y (by linarith) (by linarith)
                          have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                            rcases le_total z (2:ℝ) with hq20 | hq20
                            · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                            exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                          have hw3 : (161986357/5000000000000:ℝ) ≤ wfun (x + y) := wc_342 (x + y) (by linarith) (by linarith)
                          have hw4 : (91064031/10000000000000:ℝ) ≤ wfun (y + z) := wc_303 (y + z) (by linarith) (by linarith)
                          have hw5 : (12062377/625000000000:ℝ) ≤ wfun (x + y + z) := wc_805 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · have hw0 : (543159341/10000000000000:ℝ) ≤ wfun x := wc_144 x (by linarith) (by linarith)
                          have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_21 y (by linarith) (by linarith)
                          have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                            rcases le_total z (2:ℝ) with hq20 | hq20
                            · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                            exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                          have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_350 (x + y) (by linarith) (by linarith)
                          have hw4 : (189078223/10000000000000:ℝ) ≤ wfun (y + z) := wc_329 (y + z) (by linarith) (by linarith)
                          have hw5 : (53757489/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_828 (x + y + z) (by linarith) (by linarith)
                          linarith
                      · have hw0 : (27945219/1000000000000:ℝ) ≤ wfun x := wc_147 x (by linarith) (by linarith)
                        have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_17 y (by linarith) (by linarith)
                        have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                          rcases le_total z (2:ℝ) with hq20 | hq20
                          · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                          exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                        have hw3 : (489049523/10000000000000:ℝ) ≤ wfun (x + y) := wc_351 (x + y) (by linarith) (by linarith)
                        have hw4 : (18095851/2000000000000:ℝ) ≤ wfun (y + z) := wc_304 (y + z) (by linarith) (by linarith)
                        have hw5 : (26775111/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_830 (x + y + z) (by linarith) (by linarith)
                        linarith
                · rcases le_total y (529/512:ℝ) with hc | hc
                  · have hw0 : (13164037/10000000000000:ℝ) ≤ wfun x := wc_149 x (by linarith) (by linarith)
                    have hw1 : (1175437333/2500000000000:ℝ) ≤ wfun y := wc_12 y (by linarith) (by linarith)
                    have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                      rcases le_total z (2:ℝ) with hq20 | hq20
                      · exact le_trans (by norm_num) (wc_130 z (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                    have hw3 : (63967043/2000000000000:ℝ) ≤ wfun (x + y) := wc_344 (x + y) (by linarith) (by linarith)
                    have hw5 : (38680157/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_788 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · rcases le_total z (1023/512:ℝ) with hc | hc
                    · have hw0 : (13164037/10000000000000:ℝ) ≤ wfun x := wc_149 x (by linarith) (by linarith)
                      have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_17 y (by linarith) (by linarith)
                      have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_129 z (by linarith) (by linarith)
                      have hw3 : (685641829/10000000000000:ℝ) ≤ wfun (x + y) := wc_356 (x + y) (by linarith) (by linarith)
                      have hw4 : (231767/2000000000000:ℝ) ≤ wfun (y + z) := wc_246 (y + z) (by linarith) (by linarith)
                      have hw5 : (191511939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_807 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (13164037/10000000000000:ℝ) ≤ wfun x := wc_149 x (by linarith) (by linarith)
                      have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_17 y (by linarith) (by linarith)
                      have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                        rcases le_total z (2:ℝ) with hq20 | hq20
                        · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                      have hw3 : (685641829/10000000000000:ℝ) ≤ wfun (x + y) := wc_356 (x + y) (by linarith) (by linarith)
                      have hw4 : (18095851/2000000000000:ℝ) ≤ wfun (y + z) := wc_304 (y + z) (by linarith) (by linarith)
                      have hw5 : (354029429/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_845 (x + y + z) (by linarith) (by linarith)
                      linarith
            · rcases le_total z (509/256:ℝ) with hc | hc
              · rcases le_total x (1033/512:ℝ) with hc | hc
                · rcases le_total y (539/512:ℝ) with hc | hc
                  · have hw0 : (27945219/1000000000000:ℝ) ≤ wfun x := wc_145 x (by linarith) (by linarith)
                    have hw1 : (160574441/10000000000000:ℝ) ≤ wfun y := wc_30 y (by linarith) (by linarith)
                    have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
                    have hw3 : (685641829/10000000000000:ℝ) ≤ wfun (x + y) := wc_356 (x + y) (by linarith) (by linarith)
                    have hw5 : (3568011/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_769 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (27945219/1000000000000:ℝ) ≤ wfun x := wc_145 x (by linarith) (by linarith)
                    have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
                    have hw3 : (591930551/5000000000000:ℝ) ≤ wfun (x + y) := wc_365 (x + y) (by linarith) (by linarith)
                    have hw4 : (285997/2500000000000:ℝ) ≤ wfun (y + z) := wc_247 (y + z) (by linarith) (by linarith)
                    have hw5 : (38680157/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_788 (x + y + z) (by linarith) (by linarith)
                    linarith
                · have hw0 : (13164037/10000000000000:ℝ) ≤ wfun x := wc_149 x (by linarith) (by linarith)
                  have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
                  have hw3 : (1168886057/10000000000000:ℝ) ≤ wfun (x + y) := wc_366 (x + y) (by linarith) (by linarith)
                  have hw5 : (76765783/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_789 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total x (1033/512:ℝ) with hc | hc
                · rcases le_total y (539/512:ℝ) with hc | hc
                  · rcases le_total z (1023/512:ℝ) with hc | hc
                    · rcases le_total x (2061/1024:ℝ) with hc | hc
                      · rcases le_total y (1073/1024:ℝ) with hc | hc
                        · have hw0 : (543159341/10000000000000:ℝ) ≤ wfun x := wc_144 x (by linarith) (by linarith)
                          have hw1 : (349265369/5000000000000:ℝ) ≤ wfun y := wc_29 y (by linarith) (by linarith)
                          have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_129 z (by linarith) (by linarith)
                          have hw3 : (694482783/10000000000000:ℝ) ≤ wfun (x + y) := wc_354 (x + y) (by linarith) (by linarith)
                          have hw4 : (91064031/10000000000000:ℝ) ≤ wfun (y + z) := wc_303 (y + z) (by linarith) (by linarith)
                          have hw5 : (12062377/625000000000:ℝ) ≤ wfun (x + y + z) := wc_805 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · have hw0 : (543159341/10000000000000:ℝ) ≤ wfun x := wc_144 x (by linarith) (by linarith)
                          have hw1 : (160574441/10000000000000:ℝ) ≤ wfun y := wc_45 y (by linarith) (by linarith)
                          have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_129 z (by linarith) (by linarith)
                          have hw3 : (930293373/10000000000000:ℝ) ≤ wfun (x + y) := wc_362 (x + y) (by linarith) (by linarith)
                          have hw4 : (189078223/10000000000000:ℝ) ≤ wfun (y + z) := wc_329 (y + z) (by linarith) (by linarith)
                          have hw5 : (53757489/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_828 (x + y + z) (by linarith) (by linarith)
                          linarith
                      · have hw0 : (27945219/1000000000000:ℝ) ≤ wfun x := wc_147 x (by linarith) (by linarith)
                        have hw1 : (160574441/10000000000000:ℝ) ≤ wfun y := wc_30 y (by linarith) (by linarith)
                        have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_129 z (by linarith) (by linarith)
                        have hw3 : (924357731/10000000000000:ℝ) ≤ wfun (x + y) := wc_363 (x + y) (by linarith) (by linarith)
                        have hw4 : (18095851/2000000000000:ℝ) ≤ wfun (y + z) := wc_304 (y + z) (by linarith) (by linarith)
                        have hw5 : (26775111/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_830 (x + y + z) (by linarith) (by linarith)
                        linarith
                    · rcases le_total x (2061/1024:ℝ) with hc | hc
                      · rcases le_total y (1073/1024:ℝ) with hc | hc
                        · have hw0 : (543159341/10000000000000:ℝ) ≤ wfun x := wc_144 x (by linarith) (by linarith)
                          have hw1 : (349265369/5000000000000:ℝ) ≤ wfun y := wc_29 y (by linarith) (by linarith)
                          have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                            rcases le_total z (2:ℝ) with hq20 | hq20
                            · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                            exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                          have hw3 : (694482783/10000000000000:ℝ) ≤ wfun (x + y) := wc_354 (x + y) (by linarith) (by linarith)
                          have hw4 : (160947823/5000000000000:ℝ) ≤ wfun (y + z) := wc_343 (y + z) (by linarith) (by linarith)
                          have hw5 : (356771293/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_842 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · have hw0 : (543159341/10000000000000:ℝ) ≤ wfun x := wc_144 x (by linarith) (by linarith)
                          have hw1 : (160574441/10000000000000:ℝ) ≤ wfun y := wc_45 y (by linarith) (by linarith)
                          have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                            rcases le_total z (2:ℝ) with hq20 | hq20
                            · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                            exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                          have hw3 : (930293373/10000000000000:ℝ) ≤ wfun (x + y) := wc_362 (x + y) (by linarith) (by linarith)
                          have hw4 : (489049523/10000000000000:ℝ) ≤ wfun (y + z) := wc_351 (y + z) (by linarith) (by linarith)
                          have hw5 : (114198739/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_860 (x + y + z) (by linarith) (by linarith)
                          linarith
                      · have hw0 : (27945219/1000000000000:ℝ) ≤ wfun x := wc_147 x (by linarith) (by linarith)
                        have hw1 : (160574441/10000000000000:ℝ) ≤ wfun y := wc_30 y (by linarith) (by linarith)
                        have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                          rcases le_total z (2:ℝ) with hq20 | hq20
                          · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                          exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                        have hw3 : (924357731/10000000000000:ℝ) ≤ wfun (x + y) := wc_363 (x + y) (by linarith) (by linarith)
                        have hw4 : (63967043/2000000000000:ℝ) ≤ wfun (y + z) := wc_344 (y + z) (by linarith) (by linarith)
                        have hw5 : (91007427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_861 (x + y + z) (by linarith) (by linarith)
                        linarith
                  · have hw0 : (27945219/1000000000000:ℝ) ≤ wfun x := wc_145 x (by linarith) (by linarith)
                    have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                      rcases le_total z (2:ℝ) with hq20 | hq20
                      · exact le_trans (by norm_num) (wc_130 z (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                    have hw3 : (591930551/5000000000000:ℝ) ≤ wfun (x + y) := wc_365 (x + y) (by linarith) (by linarith)
                    have hw4 : (157881813/5000000000000:ℝ) ≤ wfun (y + z) := wc_345 (y + z) (by linarith) (by linarith)
                    have hw5 : (43914233/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_846 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total y (539/512:ℝ) with hc | hc
                  · rcases le_total z (1023/512:ℝ) with hc | hc
                    · have hw0 : (13164037/10000000000000:ℝ) ≤ wfun x := wc_149 x (by linarith) (by linarith)
                      have hw1 : (160574441/10000000000000:ℝ) ≤ wfun y := wc_30 y (by linarith) (by linarith)
                      have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_129 z (by linarith) (by linarith)
                      have hw3 : (591930551/5000000000000:ℝ) ≤ wfun (x + y) := wc_365 (x + y) (by linarith) (by linarith)
                      have hw4 : (18095851/2000000000000:ℝ) ≤ wfun (y + z) := wc_304 (y + z) (by linarith) (by linarith)
                      have hw5 : (354029429/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_845 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (13164037/10000000000000:ℝ) ≤ wfun x := wc_149 x (by linarith) (by linarith)
                      have hw1 : (160574441/10000000000000:ℝ) ≤ wfun y := wc_30 y (by linarith) (by linarith)
                      have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                        rcases le_total z (2:ℝ) with hq20 | hq20
                        · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                      have hw3 : (591930551/5000000000000:ℝ) ≤ wfun (x + y) := wc_365 (x + y) (by linarith) (by linarith)
                      have hw4 : (63967043/2000000000000:ℝ) ≤ wfun (y + z) := wc_344 (y + z) (by linarith) (by linarith)
                      have hw5 : (112866211/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_880 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (13164037/10000000000000:ℝ) ≤ wfun x := wc_149 x (by linarith) (by linarith)
                    have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                      rcases le_total z (2:ℝ) with hq20 | hq20
                      · exact le_trans (by norm_num) (wc_130 z (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                    have hw3 : (1810022563/10000000000000:ℝ) ≤ wfun (x + y) := wc_369 (x + y) (by linarith) (by linarith)
                    have hw4 : (157881813/5000000000000:ℝ) ≤ wfun (y + z) := wc_345 (y + z) (by linarith) (by linarith)
                    have hw5 : (560010683/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_881 (x + y + z) (by linarith) (by linarith)
                    linarith
          · rcases le_total y (267/256:ℝ) with hc | hc
            · rcases le_total z (509/256:ℝ) with hc | hc
              · have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_13 y (by linarith) (by linarith)
                have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
                have hw3 : (66837841/1000000000000:ℝ) ≤ wfun (x + y) := wc_358 (x + y) (by linarith) (by linarith)
                have hw5 : (1405331/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_771 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total x (1043/512:ℝ) with hc | hc
                · rcases le_total y (529/512:ℝ) with hc | hc
                  · have hw1 : (1175437333/2500000000000:ℝ) ≤ wfun y := wc_12 y (by linarith) (by linarith)
                    have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                      rcases le_total z (2:ℝ) with hq20 | hq20
                      · exact le_trans (by norm_num) (wc_130 z (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                    have hw3 : (685641829/10000000000000:ℝ) ≤ wfun (x + y) := wc_356 (x + y) (by linarith) (by linarith)
                    have hw5 : (190040129/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_808 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_17 y (by linarith) (by linarith)
                    have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                      rcases le_total z (2:ℝ) with hq20 | hq20
                      · exact le_trans (by norm_num) (wc_130 z (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                    have hw3 : (591930551/5000000000000:ℝ) ≤ wfun (x + y) := wc_365 (x + y) (by linarith) (by linarith)
                    have hw4 : (285997/2500000000000:ℝ) ≤ wfun (y + z) := wc_247 (y + z) (by linarith) (by linarith)
                    have hw5 : (43914233/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_846 (x + y + z) (by linarith) (by linarith)
                    linarith
                · have hw0 : (21355581/2500000000000:ℝ) ≤ wfun x := wc_151 x (by linarith) (by linarith)
                  have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_13 y (by linarith) (by linarith)
                  have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                    rcases le_total z (2:ℝ) with hq20 | hq20
                    · exact le_trans (by norm_num) (wc_130 z (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                  have hw3 : (1168886057/10000000000000:ℝ) ≤ wfun (x + y) := wc_366 (x + y) (by linarith) (by linarith)
                  have hw5 : (43578037/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_847 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total z (509/256:ℝ) with hc | hc
              · have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
                have hw3 : (1764735511/10000000000000:ℝ) ≤ wfun (x + y) := wc_370 (x + y) (by linarith) (by linarith)
                have hw5 : (187138697/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_810 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                  rcases le_total z (2:ℝ) with hq20 | hq20
                  · exact le_trans (by norm_num) (wc_130 z (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                have hw3 : (1764735511/10000000000000:ℝ) ≤ wfun (x + y) := wc_370 (x + y) (by linarith) (by linarith)
                have hw4 : (88186617/10000000000000:ℝ) ≤ wfun (y + z) := wc_306 (y + z) (by linarith) (by linarith)
                have hw5 : (551493311/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_883 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (519/256:ℝ) with hc | hc
          · rcases le_total y (267/256:ℝ) with hc | hc
            · rcases le_total z (519/256:ℝ) with hc | hc
              · rcases le_total x (1033/512:ℝ) with hc | hc
                · rcases le_total y (529/512:ℝ) with hc | hc
                  · have hw0 : (27945219/1000000000000:ℝ) ≤ wfun x := wc_145 x (by linarith) (by linarith)
                    have hw1 : (1175437333/2500000000000:ℝ) ≤ wfun y := wc_12 y (by linarith) (by linarith)
                    have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_146 z (by linarith) (by linarith)
                    have hw3 : (18095851/2000000000000:ℝ) ≤ wfun (x + y) := wc_304 (x + y) (by linarith) (by linarith)
                    have hw4 : (22330933/2500000000000:ℝ) ≤ wfun (y + z) := wc_305 (y + z) (by linarith) (by linarith)
                    have hw5 : (190040129/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_808 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · rcases le_total z (1033/512:ℝ) with hc | hc
                    · rcases le_total x (2061/1024:ℝ) with hc | hc
                      · have hw0 : (543159341/10000000000000:ℝ) ≤ wfun x := wc_144 x (by linarith) (by linarith)
                        have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_17 y (by linarith) (by linarith)
                        have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_145 z (by linarith) (by linarith)
                        have hw3 : (160947823/5000000000000:ℝ) ≤ wfun (x + y) := wc_343 (x + y) (by linarith) (by linarith)
                        have hw4 : (63967043/2000000000000:ℝ) ≤ wfun (y + z) := wc_344 (y + z) (by linarith) (by linarith)
                        have hw5 : (71079411/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_844 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (27945219/1000000000000:ℝ) ≤ wfun x := wc_147 x (by linarith) (by linarith)
                        have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_17 y (by linarith) (by linarith)
                        have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_145 z (by linarith) (by linarith)
                        have hw3 : (489049523/10000000000000:ℝ) ≤ wfun (x + y) := wc_351 (x + y) (by linarith) (by linarith)
                        have hw4 : (63967043/2000000000000:ℝ) ≤ wfun (y + z) := wc_344 (y + z) (by linarith) (by linarith)
                        have hw5 : (91007427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_861 (x + y + z) (by linarith) (by linarith)
                        linarith
                    · have hw0 : (27945219/1000000000000:ℝ) ≤ wfun x := wc_145 x (by linarith) (by linarith)
                      have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_17 y (by linarith) (by linarith)
                      have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_149 z (by linarith) (by linarith)
                      have hw3 : (63967043/2000000000000:ℝ) ≤ wfun (x + y) := wc_344 (x + y) (by linarith) (by linarith)
                      have hw4 : (685641829/10000000000000:ℝ) ≤ wfun (y + z) := wc_356 (y + z) (by linarith) (by linarith)
                      have hw5 : (112866211/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_880 (x + y + z) (by linarith) (by linarith)
                      linarith
                · rcases le_total y (529/512:ℝ) with hc | hc
                  · have hw0 : (13164037/10000000000000:ℝ) ≤ wfun x := wc_149 x (by linarith) (by linarith)
                    have hw1 : (1175437333/2500000000000:ℝ) ≤ wfun y := wc_12 y (by linarith) (by linarith)
                    have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_146 z (by linarith) (by linarith)
                    have hw3 : (63967043/2000000000000:ℝ) ≤ wfun (x + y) := wc_344 (x + y) (by linarith) (by linarith)
                    have hw4 : (22330933/2500000000000:ℝ) ≤ wfun (y + z) := wc_305 (y + z) (by linarith) (by linarith)
                    have hw5 : (43914233/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_846 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (13164037/10000000000000:ℝ) ≤ wfun x := wc_149 x (by linarith) (by linarith)
                    have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_17 y (by linarith) (by linarith)
                    have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_146 z (by linarith) (by linarith)
                    have hw3 : (685641829/10000000000000:ℝ) ≤ wfun (x + y) := wc_356 (x + y) (by linarith) (by linarith)
                    have hw4 : (157881813/5000000000000:ℝ) ≤ wfun (y + z) := wc_345 (y + z) (by linarith) (by linarith)
                    have hw5 : (560010683/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_881 (x + y + z) (by linarith) (by linarith)
                    linarith
              · have hw0 : (13164037/10000000000000:ℝ) ≤ wfun x := wc_146 x (by linarith) (by linarith)
                have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_13 y (by linarith) (by linarith)
                have hw3 : (88186617/10000000000000:ℝ) ≤ wfun (x + y) := wc_306 (x + y) (by linarith) (by linarith)
                have hw4 : (66837841/1000000000000:ℝ) ≤ wfun (y + z) := wc_358 (y + z) (by linarith) (by linarith)
                have hw5 : (551493311/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_883 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (519/256:ℝ) with hc | hc
              · rcases le_total x (1033/512:ℝ) with hc | hc
                · rcases le_total y (539/512:ℝ) with hc | hc
                  · rcases le_total z (1033/512:ℝ) with hc | hc
                    · have hw0 : (27945219/1000000000000:ℝ) ≤ wfun x := wc_145 x (by linarith) (by linarith)
                      have hw1 : (160574441/10000000000000:ℝ) ≤ wfun y := wc_30 y (by linarith) (by linarith)
                      have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_145 z (by linarith) (by linarith)
                      have hw3 : (685641829/10000000000000:ℝ) ≤ wfun (x + y) := wc_356 (x + y) (by linarith) (by linarith)
                      have hw4 : (685641829/10000000000000:ℝ) ≤ wfun (y + z) := wc_356 (y + z) (by linarith) (by linarith)
                      have hw5 : (112866211/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_880 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (27945219/1000000000000:ℝ) ≤ wfun x := wc_145 x (by linarith) (by linarith)
                      have hw1 : (160574441/10000000000000:ℝ) ≤ wfun y := wc_30 y (by linarith) (by linarith)
                      have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_149 z (by linarith) (by linarith)
                      have hw3 : (685641829/10000000000000:ℝ) ≤ wfun (x + y) := wc_356 (x + y) (by linarith) (by linarith)
                      have hw4 : (591930551/5000000000000:ℝ) ≤ wfun (y + z) := wc_365 (y + z) (by linarith) (by linarith)
                      have hw5 : (821066057/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_921 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (27945219/1000000000000:ℝ) ≤ wfun x := wc_145 x (by linarith) (by linarith)
                    have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_146 z (by linarith) (by linarith)
                    have hw3 : (591930551/5000000000000:ℝ) ≤ wfun (x + y) := wc_365 (x + y) (by linarith) (by linarith)
                    have hw4 : (1168886057/10000000000000:ℝ) ≤ wfun (y + z) := wc_366 (y + z) (by linarith) (by linarith)
                    have hw5 : (814792219/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_922 (x + y + z) (by linarith) (by linarith)
                    linarith
                · have hw0 : (13164037/10000000000000:ℝ) ≤ wfun x := wc_149 x (by linarith) (by linarith)
                  have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_146 z (by linarith) (by linarith)
                  have hw3 : (1168886057/10000000000000:ℝ) ≤ wfun (x + y) := wc_366 (x + y) (by linarith) (by linarith)
                  have hw4 : (66837841/1000000000000:ℝ) ≤ wfun (y + z) := wc_358 (y + z) (by linarith) (by linarith)
                  have hw5 : (404289107/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_923 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (13164037/10000000000000:ℝ) ≤ wfun x := wc_146 x (by linarith) (by linarith)
                have hw3 : (66837841/1000000000000:ℝ) ≤ wfun (x + y) := wc_358 (x + y) (by linarith) (by linarith)
                have hw4 : (1764735511/10000000000000:ℝ) ≤ wfun (y + z) := wc_370 (y + z) (by linarith) (by linarith)
                have hw5 : (1097277581/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_947 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (267/256:ℝ) with hc | hc
            · have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_13 y (by linarith) (by linarith)
              have hw3 : (66837841/1000000000000:ℝ) ≤ wfun (x + y) := wc_358 (x + y) (by linarith) (by linarith)
              have hw4 : (21491553/2500000000000:ℝ) ≤ wfun (y + z) := wc_307 (y + z) (by linarith) (by linarith)
              have hw5 : (108627463/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_884 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw3 : (1764735511/10000000000000:ℝ) ≤ wfun (x + y) := wc_370 (x + y) (by linarith) (by linarith)
              have hw4 : (162913869/2500000000000:ℝ) ≤ wfun (y + z) := wc_360 (y + z) (by linarith) (by linarith)
              have hw5 : (270178737/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_948 (x + y + z) (by linarith) (by linarith)
              linarith

set_option maxHeartbeats 20000000 in
lemma ch_71 (x y z : ℝ) (hx1 : (63/32:ℝ) ≤ x) (hx2 : x ≤ (131/64:ℝ))
    (hy1 : (17/16:ℝ) ≤ y) (hy2 : y ≤ (73/64:ℝ))
    (hz1 : (121/64:ℝ) ≤ z) (hz2 : z ≤ (131/64:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total z (63/32:ℝ) with hc | hc
  · have hw1 : (15429929/1000000000000:ℝ) ≤ wfun y := wc_63 y (by linarith) (by linarith)
    have hw2 : (795663039/1250000000000:ℝ) ≤ wfun z := wc_76 z (by linarith) (by linarith)
    have hw3 : (75856633/10000000000000:ℝ) ≤ wfun (x + y) := wc_311 (x + y) (by linarith) (by linarith)
    linarith
  · rcases le_total x (257/128:ℝ) with hc | hc
    · rcases le_total y (141/128:ℝ) with hc | hc
      · rcases le_total z (257/128:ℝ) with hc | hc
        · rcases le_total x (509/256:ℝ) with hc | hc
          · rcases le_total y (277/256:ℝ) with hc | hc
            · rcases le_total z (509/256:ℝ) with hc | hc
              · have hw0 : (396477691/1250000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
                have hw1 : (38452957/2000000000000:ℝ) ≤ wfun y := wc_61 y (by linarith) (by linarith)
                have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
                have hw3 : (88186617/10000000000000:ℝ) ≤ wfun (x + y) := wc_306 (x + y) (by linarith) (by linarith)
                have hw4 : (88186617/10000000000000:ℝ) ≤ wfun (y + z) := wc_306 (y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396477691/1250000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
                have hw1 : (38452957/2000000000000:ℝ) ≤ wfun y := wc_61 y (by linarith) (by linarith)
                have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                  rcases le_total z (2:ℝ) with hq20 | hq20
                  · exact le_trans (by norm_num) (wc_130 z (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                have hw3 : (88186617/10000000000000:ℝ) ≤ wfun (x + y) := wc_306 (x + y) (by linarith) (by linarith)
                have hw4 : (66837841/1000000000000:ℝ) ≤ wfun (y + z) := wc_358 (y + z) (by linarith) (by linarith)
                have hw5 : (1405331/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_771 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (396477691/1250000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
              have hw1 : (4137262453/10000000000000:ℝ) ≤ wfun y := wc_66 y (by linarith) (by linarith)
              have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                rcases le_total z (2:ℝ) with hq20 | hq20
                · exact le_trans (by norm_num) (wc_90 z (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
              have hw3 : (66837841/1000000000000:ℝ) ≤ wfun (x + y) := wc_358 (x + y) (by linarith) (by linarith)
              have hw4 : (162913869/2500000000000:ℝ) ≤ wfun (y + z) := wc_360 (y + z) (by linarith) (by linarith)
              have hw5 : (13838751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_772 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (277/256:ℝ) with hc | hc
            · rcases le_total z (509/256:ℝ) with hc | hc
              · have hw0 : (179073511/2000000000000:ℝ) ≤ wfun x := by
                  rcases le_total x (2:ℝ) with hq00 | hq00
                  · exact le_trans (by norm_num) (wc_130 x (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_141 x (by linarith) (by linarith))
                have hw1 : (38452957/2000000000000:ℝ) ≤ wfun y := wc_61 y (by linarith) (by linarith)
                have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
                have hw3 : (66837841/1000000000000:ℝ) ≤ wfun (x + y) := wc_358 (x + y) (by linarith) (by linarith)
                have hw4 : (88186617/10000000000000:ℝ) ≤ wfun (y + z) := wc_306 (y + z) (by linarith) (by linarith)
                have hw5 : (1405331/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_771 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (179073511/2000000000000:ℝ) ≤ wfun x := by
                  rcases le_total x (2:ℝ) with hq00 | hq00
                  · exact le_trans (by norm_num) (wc_130 x (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_141 x (by linarith) (by linarith))
                have hw1 : (38452957/2000000000000:ℝ) ≤ wfun y := wc_61 y (by linarith) (by linarith)
                have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                  rcases le_total z (2:ℝ) with hq20 | hq20
                  · exact le_trans (by norm_num) (wc_130 z (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                have hw3 : (66837841/1000000000000:ℝ) ≤ wfun (x + y) := wc_358 (x + y) (by linarith) (by linarith)
                have hw4 : (66837841/1000000000000:ℝ) ≤ wfun (y + z) := wc_358 (y + z) (by linarith) (by linarith)
                have hw5 : (187138697/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_810 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (179073511/2000000000000:ℝ) ≤ wfun x := by
                rcases le_total x (2:ℝ) with hq00 | hq00
                · exact le_trans (by norm_num) (wc_130 x (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_141 x (by linarith) (by linarith))
              have hw1 : (4137262453/10000000000000:ℝ) ≤ wfun y := wc_66 y (by linarith) (by linarith)
              have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                rcases le_total z (2:ℝ) with hq20 | hq20
                · exact le_trans (by norm_num) (wc_90 z (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
              have hw3 : (1764735511/10000000000000:ℝ) ≤ wfun (x + y) := wc_370 (x + y) (by linarith) (by linarith)
              have hw4 : (162913869/2500000000000:ℝ) ≤ wfun (y + z) := wc_360 (y + z) (by linarith) (by linarith)
              have hw5 : (5759139/312500000000:ℝ) ≤ wfun (x + y + z) := wc_811 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (509/256:ℝ) with hc | hc
          · have hw0 : (396477691/1250000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
            have hw1 : (44604923/2500000000000:ℝ) ≤ wfun y := wc_62 y (by linarith) (by linarith)
            have hw3 : (21491553/2500000000000:ℝ) ≤ wfun (x + y) := wc_307 (x + y) (by linarith) (by linarith)
            have hw4 : (419583999/2500000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
            have hw5 : (90750063/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_812 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (179073511/2000000000000:ℝ) ≤ wfun x := by
              rcases le_total x (2:ℝ) with hq00 | hq00
              · exact le_trans (by norm_num) (wc_130 x (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_141 x (by linarith) (by linarith))
            have hw1 : (44604923/2500000000000:ℝ) ≤ wfun y := wc_62 y (by linarith) (by linarith)
            have hw3 : (162913869/2500000000000:ℝ) ≤ wfun (x + y) := wc_360 (x + y) (by linarith) (by linarith)
            have hw4 : (419583999/2500000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
            have hw5 : (534939039/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_885 (x + y + z) (by linarith) (by linarith)
            linarith
      · have hw0 : (179073511/2000000000000:ℝ) ≤ wfun x := by
          rcases le_total x (2:ℝ) with hq00 | hq00
          · exact le_trans (by norm_num) (wc_90 x (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_141 x (by linarith) (by linarith))
        have hw1 : (11778340313/10000000000000:ℝ) ≤ wfun y := wc_67 y (by linarith) (by linarith)
        have hw3 : (419583999/2500000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
        have hw4 : (798582451/5000000000000:ℝ) ≤ wfun (y + z) := wc_374 (y + z) (by linarith) (by linarith)
        have hw5 : (21679333/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_813 (x + y + z) (by linarith) (by linarith)
        linarith
    · rcases le_total y (141/128:ℝ) with hc | hc
      · rcases le_total z (257/128:ℝ) with hc | hc
        · rcases le_total x (519/256:ℝ) with hc | hc
          · rcases le_total y (277/256:ℝ) with hc | hc
            · have hw0 : (13164037/10000000000000:ℝ) ≤ wfun x := wc_146 x (by linarith) (by linarith)
              have hw1 : (38452957/2000000000000:ℝ) ≤ wfun y := wc_61 y (by linarith) (by linarith)
              have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                rcases le_total z (2:ℝ) with hq20 | hq20
                · exact le_trans (by norm_num) (wc_90 z (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
              have hw3 : (1764735511/10000000000000:ℝ) ≤ wfun (x + y) := wc_370 (x + y) (by linarith) (by linarith)
              have hw4 : (21491553/2500000000000:ℝ) ≤ wfun (y + z) := wc_307 (y + z) (by linarith) (by linarith)
              have hw5 : (5759139/312500000000:ℝ) ≤ wfun (x + y + z) := wc_811 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (13164037/10000000000000:ℝ) ≤ wfun x := wc_146 x (by linarith) (by linarith)
              have hw1 : (4137262453/10000000000000:ℝ) ≤ wfun y := wc_66 y (by linarith) (by linarith)
              have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                rcases le_total z (2:ℝ) with hq20 | hq20
                · exact le_trans (by norm_num) (wc_90 z (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
              have hw3 : (1670535297/5000000000000:ℝ) ≤ wfun (x + y) := wc_378 (x + y) (by linarith) (by linarith)
              have hw4 : (162913869/2500000000000:ℝ) ≤ wfun (y + z) := wc_360 (y + z) (by linarith) (by linarith)
              have hw5 : (108627463/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_884 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw1 : (44604923/2500000000000:ℝ) ≤ wfun y := wc_62 y (by linarith) (by linarith)
            have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
              rcases le_total z (2:ℝ) with hq20 | hq20
              · exact le_trans (by norm_num) (wc_90 z (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
            have hw3 : (1629257293/5000000000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
            have hw4 : (20953831/2500000000000:ℝ) ≤ wfun (y + z) := wc_308 (y + z) (by linarith) (by linarith)
            have hw5 : (534939039/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_885 (x + y + z) (by linarith) (by linarith)
            linarith
        · have hw1 : (44604923/2500000000000:ℝ) ≤ wfun y := wc_62 y (by linarith) (by linarith)
          have hw3 : (419583999/2500000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
          have hw4 : (419583999/2500000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
          have hw5 : (1048517003/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_949 (x + y + z) (by linarith) (by linarith)
          linarith
      · have hw1 : (11778340313/10000000000000:ℝ) ≤ wfun y := wc_67 y (by linarith) (by linarith)
        have hw3 : (5096134953/10000000000000:ℝ) ≤ wfun (x + y) := wc_384 (x + y) (by linarith) (by linarith)
        have hw4 : (798582451/5000000000000:ℝ) ≤ wfun (y + z) := wc_374 (y + z) (by linarith) (by linarith)
        have hw5 : (1017509707/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_950 (x + y + z) (by linarith) (by linarith)
        linarith

end Zeta23Ext.Bridge.FourPoint
