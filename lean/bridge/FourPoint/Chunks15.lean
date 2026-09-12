import FourPoint.Cells

/-! Chunk module 15 of 16 of the three-dimensional table.  Each lemma is one
subtree of at most 110 leaves of one box's bisection tree; `FourPoint/Boxes.lean` routes
the box down to them.  Cutting the tree this way gives each subtree its own
heartbeat budget and lets `lake` compile them in parallel. -/

noncomputable section
namespace Zeta23Ext.Bridge.FourPoint

set_option maxHeartbeats 20000000 in
lemma ch_10 (x y z : ℝ) (hx1 : (529/512:ℝ) ≤ x) (hx2 : x ≤ (1063/1024:ℝ))
    (hy1 : (1013/512:ℝ) ≤ y) (hy2 : y ≤ (509/256:ℝ))
    (hz1 : (267/256:ℝ) ≤ z) (hz2 : z ≤ (539/512:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total y (2031/1024:ℝ) with hc | hc
  · rcases le_total z (1073/1024:ℝ) with hc | hc
    · rcases le_total x (2121/2048:ℝ) with hc | hc
      · have hw0 : (1888462017/5000000000000:ℝ) ≤ wfun x := wc_15 x (by linarith) (by linarith)
        have hw1 : (200253263/500000000000:ℝ) ≤ wfun y := wc_104 y (by linarith) (by linarith)
        have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
        have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_232 (x + y) (by linarith) (by linarith)
        have hw4 : (293481/2500000000000:ℝ) ≤ wfun (y + z) := wc_244 (y + z) (by linarith) (by linarith)
        have hw5 : (323709737/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_544 (x + y + z) (by linarith) (by linarith)
        linarith
      · rcases le_total y (4057/2048:ℝ) with hc | hc
        · rcases le_total z (2141/2048:ℝ) with hc | hc
          · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
            have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_103 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
            have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_234 (x + y) (by linarith) (by linarith)
            have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_242 (y + z) (by linarith) (by linarith)
            have hw5 : (183045519/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_557 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
            have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_103 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_234 (x + y) (by linarith) (by linarith)
            have hw4 : (2076333/2000000000000:ℝ) ≤ wfun (y + z) := wc_256 (y + z) (by linarith) (by linarith)
            have hw5 : (12788137/156250000000:ℝ) ≤ wfun (x + y + z) := wc_560 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (2141/2048:ℝ) with hc | hc
          · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
            have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_112 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
            have hw4 : (2076333/2000000000000:ℝ) ≤ wfun (y + z) := wc_256 (y + z) (by linarith) (by linarith)
            have hw5 : (12788137/156250000000:ℝ) ≤ wfun (x + y + z) := wc_560 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
            have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_112 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw4 : (14329561/5000000000000:ℝ) ≤ wfun (y + z) := wc_270 (y + z) (by linarith) (by linarith)
            have hw5 : (56830383/625000000000:ℝ) ≤ wfun (x + y + z) := wc_571 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total x (2121/2048:ℝ) with hc | hc
      · have hw0 : (1888462017/5000000000000:ℝ) ≤ wfun x := wc_15 x (by linarith) (by linarith)
        have hw1 : (200253263/500000000000:ℝ) ≤ wfun y := wc_104 y (by linarith) (by linarith)
        have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
        have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_232 (x + y) (by linarith) (by linarith)
        have hw4 : (28474189/10000000000000:ℝ) ≤ wfun (y + z) := wc_272 (y + z) (by linarith) (by linarith)
        have hw5 : (407254991/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_562 (x + y + z) (by linarith) (by linarith)
        linarith
      · rcases le_total y (4057/2048:ℝ) with hc | hc
        · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
          have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_103 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
          have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_234 (x + y) (by linarith) (by linarith)
          have hw4 : (7141617/2500000000000:ℝ) ≤ wfun (y + z) := wc_271 (y + z) (by linarith) (by linarith)
          have hw5 : (907100611/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_572 (x + y + z) (by linarith) (by linarith)
          linarith
        · rcases le_total z (2151/2048:ℝ) with hc | hc
          · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
            have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_112 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
            have hw4 : (55964847/10000000000000:ℝ) ≤ wfun (y + z) := wc_286 (y + z) (by linarith) (by linarith)
            have hw5 : (1004679561/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_581 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
            have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_112 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw4 : (92247841/10000000000000:ℝ) ≤ wfun (y + z) := wc_300 (y + z) (by linarith) (by linarith)
            have hw5 : (8629543/78125000000:ℝ) ≤ wfun (x + y + z) := wc_597 (x + y + z) (by linarith) (by linarith)
            linarith
  · rcases le_total z (1073/1024:ℝ) with hc | hc
    · rcases le_total x (2121/2048:ℝ) with hc | hc
      · rcases le_total y (4067/2048:ℝ) with hc | hc
        · have hw0 : (1888462017/5000000000000:ℝ) ≤ wfun x := wc_15 x (by linarith) (by linarith)
          have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_119 y (by linarith) (by linarith)
          have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
          have hw4 : (7141617/2500000000000:ℝ) ≤ wfun (y + z) := wc_271 (y + z) (by linarith) (by linarith)
          have hw5 : (25514763/312500000000:ℝ) ≤ wfun (x + y + z) := wc_561 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (1888462017/5000000000000:ℝ) ≤ wfun x := wc_15 x (by linarith) (by linarith)
          have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
          have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
          have hw4 : (27892031/5000000000000:ℝ) ≤ wfun (y + z) := wc_287 (y + z) (by linarith) (by linarith)
          have hw5 : (907100611/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_572 (x + y + z) (by linarith) (by linarith)
          linarith
      · rcases le_total y (4067/2048:ℝ) with hc | hc
        · rcases le_total z (2141/2048:ℝ) with hc | hc
          · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
            have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_119 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
            have hw4 : (14329561/5000000000000:ℝ) ≤ wfun (y + z) := wc_270 (y + z) (by linarith) (by linarith)
            have hw5 : (56830383/625000000000:ℝ) ≤ wfun (x + y + z) := wc_571 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
            have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_119 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw4 : (55964847/10000000000000:ℝ) ≤ wfun (y + z) := wc_286 (y + z) (by linarith) (by linarith)
            have hw5 : (1004679561/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_581 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (2141/2048:ℝ) with hc | hc
          · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
            have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
            have hw3 : (1181561/10000000000000:ℝ) ≤ wfun (x + y) := wc_242 (x + y) (by linarith) (by linarith)
            have hw4 : (55964847/10000000000000:ℝ) ≤ wfun (y + z) := wc_286 (y + z) (by linarith) (by linarith)
            have hw5 : (1004679561/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_581 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
            have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (1181561/10000000000000:ℝ) ≤ wfun (x + y) := wc_242 (x + y) (by linarith) (by linarith)
            have hw4 : (92247841/10000000000000:ℝ) ≤ wfun (y + z) := wc_300 (y + z) (by linarith) (by linarith)
            have hw5 : (8629543/78125000000:ℝ) ≤ wfun (x + y + z) := wc_597 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total x (2121/2048:ℝ) with hc | hc
      · have hw0 : (1888462017/5000000000000:ℝ) ≤ wfun x := wc_15 x (by linarith) (by linarith)
        have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_120 y (by linarith) (by linarith)
        have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
        have hw4 : (11456693/1250000000000:ℝ) ≤ wfun (y + z) := wc_302 (y + z) (by linarith) (by linarith)
        have hw5 : (199972023/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_583 (x + y + z) (by linarith) (by linarith)
        linarith
      · rcases le_total y (4067/2048:ℝ) with hc | hc
        · rcases le_total z (2151/2048:ℝ) with hc | hc
          · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
            have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_119 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
            have hw4 : (92247841/10000000000000:ℝ) ≤ wfun (y + z) := wc_300 (y + z) (by linarith) (by linarith)
            have hw5 : (8629543/78125000000:ℝ) ≤ wfun (x + y + z) := wc_597 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
            have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_119 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw4 : (13745521/1000000000000:ℝ) ≤ wfun (y + z) := wc_320 (y + z) (by linarith) (by linarith)
            have hw5 : (1208951451/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_610 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (2151/2048:ℝ) with hc | hc
          · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
            have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
            have hw3 : (1181561/10000000000000:ℝ) ≤ wfun (x + y) := wc_242 (x + y) (by linarith) (by linarith)
            have hw4 : (13745521/1000000000000:ℝ) ≤ wfun (y + z) := wc_320 (y + z) (by linarith) (by linarith)
            have hw5 : (1208951451/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_610 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
            have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (1181561/10000000000000:ℝ) ≤ wfun (x + y) := wc_242 (x + y) (by linarith) (by linarith)
            have hw4 : (23941523/1250000000000:ℝ) ≤ wfun (y + z) := wc_326 (y + z) (by linarith) (by linarith)
            have hw5 : (263549591/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_631 (x + y + z) (by linarith) (by linarith)
            linarith

set_option maxHeartbeats 20000000 in
lemma ch_14 (x y z : ℝ) (hx1 : (131/128:ℝ) ≤ x) (hx2 : x ≤ (267/256:ℝ))
    (hy1 : (509/256:ℝ) ≤ y) (hy2 : y ≤ (257/128:ℝ))
    (hz1 : (131/128:ℝ) ≤ z) (hz2 : z ≤ (267/256:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (529/512:ℝ) with hc | hc
  · rcases le_total y (1023/512:ℝ) with hc | hc
    · rcases le_total z (529/512:ℝ) with hc | hc
      · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
        have hw1 : (1865845891/10000000000000:ℝ) ≤ wfun y := wc_129 y (by linarith) (by linarith)
        have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
        have hw5 : (164514637/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_509 (x + y + z) (by linarith) (by linarith)
        linarith
      · rcases le_total x (1053/1024:ℝ) with hc | hc
        · have hw0 : (3436255003/5000000000000:ℝ) ≤ wfun x := wc_11 x (by linarith) (by linarith)
          have hw1 : (1865845891/10000000000000:ℝ) ≤ wfun y := wc_129 y (by linarith) (by linarith)
          have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
          have hw4 : (231767/2000000000000:ℝ) ≤ wfun (y + z) := wc_246 (y + z) (by linarith) (by linarith)
          have hw5 : (182379599/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_529 (x + y + z) (by linarith) (by linarith)
          linarith
        · rcases le_total y (2041/1024:ℝ) with hc | hc
          · rcases le_total z (1063/1024:ℝ) with hc | hc
            · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_14 x (by linarith) (by linarith)
              have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
              have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
              have hw4 : (293481/2500000000000:ℝ) ≤ wfun (y + z) := wc_244 (y + z) (by linarith) (by linarith)
              have hw5 : (99536523/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_537 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_14 x (by linarith) (by linarith)
              have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
              have hw4 : (28474189/10000000000000:ℝ) ≤ wfun (y + z) := wc_272 (y + z) (by linarith) (by linarith)
              have hw5 : (645862429/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_545 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (1063/1024:ℝ) with hc | hc
            · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_14 x (by linarith) (by linarith)
              have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
              have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
              have hw3 : (293481/2500000000000:ℝ) ≤ wfun (x + y) := wc_244 (x + y) (by linarith) (by linarith)
              have hw4 : (28474189/10000000000000:ℝ) ≤ wfun (y + z) := wc_272 (y + z) (by linarith) (by linarith)
              have hw5 : (645862429/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_545 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_14 x (by linarith) (by linarith)
              have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
              have hw3 : (293481/2500000000000:ℝ) ≤ wfun (x + y) := wc_244 (x + y) (by linarith) (by linarith)
              have hw4 : (11456693/1250000000000:ℝ) ≤ wfun (y + z) := wc_302 (y + z) (by linarith) (by linarith)
              have hw5 : (812553443/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_563 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total z (529/512:ℝ) with hc | hc
      · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
        have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
          rcases le_total y (2:ℝ) with hq10 | hq10
          · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
        have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
        have hw3 : (231767/2000000000000:ℝ) ≤ wfun (x + y) := wc_246 (x + y) (by linarith) (by linarith)
        have hw4 : (231767/2000000000000:ℝ) ≤ wfun (y + z) := wc_246 (y + z) (by linarith) (by linarith)
        have hw5 : (90752099/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_530 (x + y + z) (by linarith) (by linarith)
        linarith
      · rcases le_total x (1053/1024:ℝ) with hc | hc
        · have hw0 : (3436255003/5000000000000:ℝ) ≤ wfun x := wc_11 x (by linarith) (by linarith)
          have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
            rcases le_total y (2:ℝ) with hq10 | hq10
            · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
          have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
          have hw3 : (1166349/10000000000000:ℝ) ≤ wfun (x + y) := wc_245 (x + y) (by linarith) (by linarith)
          have hw4 : (18095851/2000000000000:ℝ) ≤ wfun (y + z) := wc_304 (y + z) (by linarith) (by linarith)
          have hw5 : (79960111/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_547 (x + y + z) (by linarith) (by linarith)
          linarith
        · rcases le_total y (2051/1024:ℝ) with hc | hc
          · rcases le_total z (1063/1024:ℝ) with hc | hc
            · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_14 x (by linarith) (by linarith)
              have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
                rcases le_total y (2:ℝ) with hq10 | hq10
                · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_140 y (by linarith) (by linarith))
              have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
              have hw3 : (28474189/10000000000000:ℝ) ≤ wfun (x + y) := wc_272 (x + y) (by linarith) (by linarith)
              have hw4 : (11456693/1250000000000:ℝ) ≤ wfun (y + z) := wc_302 (y + z) (by linarith) (by linarith)
              have hw5 : (812553443/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_563 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_14 x (by linarith) (by linarith)
              have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
                rcases le_total y (2:ℝ) with hq10 | hq10
                · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_140 y (by linarith) (by linarith))
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
              have hw3 : (28474189/10000000000000:ℝ) ≤ wfun (x + y) := wc_272 (x + y) (by linarith) (by linarith)
              have hw4 : (190300253/10000000000000:ℝ) ≤ wfun (y + z) := wc_328 (y + z) (by linarith) (by linarith)
              have hw5 : (249365309/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_584 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_14 x (by linarith) (by linarith)
            have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
            have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
            have hw3 : (11456693/1250000000000:ℝ) ≤ wfun (x + y) := wc_302 (x + y) (by linarith) (by linarith)
            have hw4 : (189078223/10000000000000:ℝ) ≤ wfun (y + z) := wc_329 (y + z) (by linarith) (by linarith)
            have hw5 : (198537007/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_585 (x + y + z) (by linarith) (by linarith)
            linarith
  · rcases le_total y (1023/512:ℝ) with hc | hc
    · rcases le_total z (529/512:ℝ) with hc | hc
      · rcases le_total x (1063/1024:ℝ) with hc | hc
        · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_16 x (by linarith) (by linarith)
          have hw1 : (1865845891/10000000000000:ℝ) ≤ wfun y := wc_129 y (by linarith) (by linarith)
          have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
          have hw3 : (1166349/10000000000000:ℝ) ≤ wfun (x + y) := wc_245 (x + y) (by linarith) (by linarith)
          have hw5 : (182379599/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_529 (x + y + z) (by linarith) (by linarith)
          linarith
        · rcases le_total y (2041/1024:ℝ) with hc | hc
          · rcases le_total z (1053/1024:ℝ) with hc | hc
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
              have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
              have hw2 : (3436255003/5000000000000:ℝ) ≤ wfun z := wc_11 z (by linarith) (by linarith)
              have hw3 : (28474189/10000000000000:ℝ) ≤ wfun (x + y) := wc_272 (x + y) (by linarith) (by linarith)
              have hw5 : (99536523/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_537 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
              have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
              have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_14 z (by linarith) (by linarith)
              have hw3 : (28474189/10000000000000:ℝ) ≤ wfun (x + y) := wc_272 (x + y) (by linarith) (by linarith)
              have hw5 : (645862429/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_545 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (1053/1024:ℝ) with hc | hc
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
              have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
              have hw2 : (3436255003/5000000000000:ℝ) ≤ wfun z := wc_11 z (by linarith) (by linarith)
              have hw3 : (11456693/1250000000000:ℝ) ≤ wfun (x + y) := wc_302 (x + y) (by linarith) (by linarith)
              have hw5 : (645862429/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_545 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
              have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
              have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_14 z (by linarith) (by linarith)
              have hw3 : (11456693/1250000000000:ℝ) ≤ wfun (x + y) := wc_302 (x + y) (by linarith) (by linarith)
              have hw4 : (293481/2500000000000:ℝ) ≤ wfun (y + z) := wc_244 (y + z) (by linarith) (by linarith)
              have hw5 : (812553443/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_563 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (1063/1024:ℝ) with hc | hc
        · rcases le_total y (2041/1024:ℝ) with hc | hc
          · rcases le_total z (1063/1024:ℝ) with hc | hc
            · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_16 x (by linarith) (by linarith)
              have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
              have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
              have hw3 : (293481/2500000000000:ℝ) ≤ wfun (x + y) := wc_244 (x + y) (by linarith) (by linarith)
              have hw4 : (293481/2500000000000:ℝ) ≤ wfun (y + z) := wc_244 (y + z) (by linarith) (by linarith)
              have hw5 : (645862429/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_545 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (2121/2048:ℝ) with hc | hc
              · have hw0 : (1888462017/5000000000000:ℝ) ≤ wfun x := wc_15 x (by linarith) (by linarith)
                have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
                have hw3 : (235547/2000000000000:ℝ) ≤ wfun (x + y) := wc_243 (x + y) (by linarith) (by linarith)
                have hw4 : (28474189/10000000000000:ℝ) ≤ wfun (y + z) := wc_272 (y + z) (by linarith) (by linarith)
                have hw5 : (407254991/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_562 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total y (4077/2048:ℝ) with hc | hc
                · rcases le_total z (2131/2048:ℝ) with hc | hc
                  · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
                    have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_127 y (by linarith) (by linarith)
                    have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
                    have hw3 : (2076333/2000000000000:ℝ) ≤ wfun (x + y) := wc_256 (x + y) (by linarith) (by linarith)
                    have hw4 : (14329561/5000000000000:ℝ) ≤ wfun (y + z) := wc_270 (y + z) (by linarith) (by linarith)
                    have hw5 : (56830383/625000000000:ℝ) ≤ wfun (x + y + z) := wc_571 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
                    have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_127 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                    have hw3 : (2076333/2000000000000:ℝ) ≤ wfun (x + y) := wc_256 (x + y) (by linarith) (by linarith)
                    have hw4 : (55964847/10000000000000:ℝ) ≤ wfun (y + z) := wc_286 (y + z) (by linarith) (by linarith)
                    have hw5 : (1004679561/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_581 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total z (2131/2048:ℝ) with hc | hc
                  · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
                    have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_133 y (by linarith) (by linarith)
                    have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
                    have hw3 : (14329561/5000000000000:ℝ) ≤ wfun (x + y) := wc_270 (x + y) (by linarith) (by linarith)
                    have hw4 : (55964847/10000000000000:ℝ) ≤ wfun (y + z) := wc_286 (y + z) (by linarith) (by linarith)
                    have hw5 : (1004679561/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_581 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
                    have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_133 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                    have hw3 : (14329561/5000000000000:ℝ) ≤ wfun (x + y) := wc_270 (x + y) (by linarith) (by linarith)
                    have hw4 : (92247841/10000000000000:ℝ) ≤ wfun (y + z) := wc_300 (y + z) (by linarith) (by linarith)
                    have hw5 : (8629543/78125000000:ℝ) ≤ wfun (x + y + z) := wc_597 (x + y + z) (by linarith) (by linarith)
                    linarith
          · rcases le_total z (1063/1024:ℝ) with hc | hc
            · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_16 x (by linarith) (by linarith)
              have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
              have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
              have hw3 : (28474189/10000000000000:ℝ) ≤ wfun (x + y) := wc_272 (x + y) (by linarith) (by linarith)
              have hw4 : (28474189/10000000000000:ℝ) ≤ wfun (y + z) := wc_272 (y + z) (by linarith) (by linarith)
              have hw5 : (812553443/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_563 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (2121/2048:ℝ) with hc | hc
              · have hw0 : (1888462017/5000000000000:ℝ) ≤ wfun x := wc_15 x (by linarith) (by linarith)
                have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
                have hw3 : (7141617/2500000000000:ℝ) ≤ wfun (x + y) := wc_271 (x + y) (by linarith) (by linarith)
                have hw4 : (11456693/1250000000000:ℝ) ≤ wfun (y + z) := wc_302 (y + z) (by linarith) (by linarith)
                have hw5 : (199972023/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_583 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total y (4087/2048:ℝ) with hc | hc
                · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
                  have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_135 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
                  have hw3 : (55964847/10000000000000:ℝ) ≤ wfun (x + y) := wc_286 (x + y) (by linarith) (by linarith)
                  have hw4 : (22987523/2500000000000:ℝ) ≤ wfun (y + z) := wc_301 (y + z) (by linarith) (by linarith)
                  have hw5 : (55096489/500000000000:ℝ) ≤ wfun (x + y + z) := wc_598 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
                  have hw1 : (1868712167/10000000000000:ℝ) ≤ wfun y := wc_137 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
                  have hw3 : (92247841/10000000000000:ℝ) ≤ wfun (x + y) := wc_300 (x + y) (by linarith) (by linarith)
                  have hw4 : (2140811/156250000000:ℝ) ≤ wfun (y + z) := wc_321 (y + z) (by linarith) (by linarith)
                  have hw5 : (1206050917/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_611 (x + y + z) (by linarith) (by linarith)
                  linarith
        · rcases le_total y (2041/1024:ℝ) with hc | hc
          · rcases le_total z (1063/1024:ℝ) with hc | hc
            · rcases le_total x (2131/2048:ℝ) with hc | hc
              · rcases le_total y (4077/2048:ℝ) with hc | hc
                · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
                  have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_127 y (by linarith) (by linarith)
                  have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
                  have hw3 : (14329561/5000000000000:ℝ) ≤ wfun (x + y) := wc_270 (x + y) (by linarith) (by linarith)
                  have hw4 : (235547/2000000000000:ℝ) ≤ wfun (y + z) := wc_243 (y + z) (by linarith) (by linarith)
                  have hw5 : (25514763/312500000000:ℝ) ≤ wfun (x + y + z) := wc_561 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
                  have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_133 y (by linarith) (by linarith)
                  have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
                  have hw3 : (55964847/10000000000000:ℝ) ≤ wfun (x + y) := wc_286 (x + y) (by linarith) (by linarith)
                  have hw4 : (5174037/5000000000000:ℝ) ≤ wfun (y + z) := wc_257 (y + z) (by linarith) (by linarith)
                  have hw5 : (907100611/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_572 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (4077/2048:ℝ) with hc | hc
                · rcases le_total z (2121/2048:ℝ) with hc | hc
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
                    have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_127 y (by linarith) (by linarith)
                    have hw2 : (1888462017/5000000000000:ℝ) ≤ wfun z := wc_15 z (by linarith) (by linarith)
                    have hw3 : (55964847/10000000000000:ℝ) ≤ wfun (x + y) := wc_286 (x + y) (by linarith) (by linarith)
                    have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_242 (y + z) (by linarith) (by linarith)
                    have hw5 : (56830383/625000000000:ℝ) ≤ wfun (x + y + z) := wc_571 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
                    have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_127 y (by linarith) (by linarith)
                    have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
                    have hw3 : (55964847/10000000000000:ℝ) ≤ wfun (x + y) := wc_286 (x + y) (by linarith) (by linarith)
                    have hw4 : (2076333/2000000000000:ℝ) ≤ wfun (y + z) := wc_256 (y + z) (by linarith) (by linarith)
                    have hw5 : (1004679561/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_581 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total z (2121/2048:ℝ) with hc | hc
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
                    have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_133 y (by linarith) (by linarith)
                    have hw2 : (1888462017/5000000000000:ℝ) ≤ wfun z := wc_15 z (by linarith) (by linarith)
                    have hw3 : (92247841/10000000000000:ℝ) ≤ wfun (x + y) := wc_300 (x + y) (by linarith) (by linarith)
                    have hw4 : (2076333/2000000000000:ℝ) ≤ wfun (y + z) := wc_256 (y + z) (by linarith) (by linarith)
                    have hw5 : (1004679561/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_581 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
                    have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_133 y (by linarith) (by linarith)
                    have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
                    have hw3 : (92247841/10000000000000:ℝ) ≤ wfun (x + y) := wc_300 (x + y) (by linarith) (by linarith)
                    have hw4 : (14329561/5000000000000:ℝ) ≤ wfun (y + z) := wc_270 (y + z) (by linarith) (by linarith)
                    have hw5 : (8629543/78125000000:ℝ) ≤ wfun (x + y + z) := wc_597 (x + y + z) (by linarith) (by linarith)
                    linarith
            · rcases le_total x (2131/2048:ℝ) with hc | hc
              · rcases le_total y (4077/2048:ℝ) with hc | hc
                · rcases le_total z (2131/2048:ℝ) with hc | hc
                  · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
                    have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_127 y (by linarith) (by linarith)
                    have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
                    have hw3 : (14329561/5000000000000:ℝ) ≤ wfun (x + y) := wc_270 (x + y) (by linarith) (by linarith)
                    have hw4 : (14329561/5000000000000:ℝ) ≤ wfun (y + z) := wc_270 (y + z) (by linarith) (by linarith)
                    have hw5 : (1004679561/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_581 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · rcases le_total x (4257/4096:ℝ) with hc | hc
                    · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
                      have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_127 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                      have hw3 : (2870559/1000000000000:ℝ) ≤ wfun (x + y) := wc_269 (x + y) (by linarith) (by linarith)
                      have hw4 : (55964847/10000000000000:ℝ) ≤ wfun (y + z) := wc_286 (y + z) (by linarith) (by linarith)
                      have hw5 : (1105910359/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_596 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_22 x (by linarith) (by linarith)
                      have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_127 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                      have hw3 : (20626673/5000000000000:ℝ) ≤ wfun (x + y) := wc_279 (x + y) (by linarith) (by linarith)
                      have hw4 : (55964847/10000000000000:ℝ) ≤ wfun (y + z) := wc_286 (y + z) (by linarith) (by linarith)
                      have hw5 : (1157601093/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_604 (x + y + z) (by linarith) (by linarith)
                      linarith
                · rcases le_total z (2131/2048:ℝ) with hc | hc
                  · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
                    have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_133 y (by linarith) (by linarith)
                    have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
                    have hw3 : (55964847/10000000000000:ℝ) ≤ wfun (x + y) := wc_286 (x + y) (by linarith) (by linarith)
                    have hw4 : (55964847/10000000000000:ℝ) ≤ wfun (y + z) := wc_286 (y + z) (by linarith) (by linarith)
                    have hw5 : (8629543/78125000000:ℝ) ≤ wfun (x + y + z) := wc_597 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · rcases le_total x (4257/4096:ℝ) with hc | hc
                    · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
                      have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_133 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                      have hw3 : (28027757/5000000000000:ℝ) ≤ wfun (x + y) := wc_285 (x + y) (by linarith) (by linarith)
                      have hw4 : (92247841/10000000000000:ℝ) ≤ wfun (y + z) := wc_300 (y + z) (by linarith) (by linarith)
                      have hw5 : (121040499/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_609 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_22 x (by linarith) (by linarith)
                      have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_133 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                      have hw3 : (18276411/2500000000000:ℝ) ≤ wfun (x + y) := wc_293 (x + y) (by linarith) (by linarith)
                      have hw4 : (92247841/10000000000000:ℝ) ≤ wfun (y + z) := wc_300 (y + z) (by linarith) (by linarith)
                      have hw5 : (1264316833/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_622 (x + y + z) (by linarith) (by linarith)
                      linarith
              · rcases le_total y (4077/2048:ℝ) with hc | hc
                · rcases le_total z (2131/2048:ℝ) with hc | hc
                  · rcases le_total x (4267/4096:ℝ) with hc | hc
                    · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                      have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_127 y (by linarith) (by linarith)
                      have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
                      have hw3 : (28027757/5000000000000:ℝ) ≤ wfun (x + y) := wc_285 (x + y) (by linarith) (by linarith)
                      have hw4 : (14329561/5000000000000:ℝ) ≤ wfun (y + z) := wc_270 (y + z) (by linarith) (by linarith)
                      have hw5 : (1105910359/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_596 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                      have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_127 y (by linarith) (by linarith)
                      have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
                      have hw3 : (18276411/2500000000000:ℝ) ≤ wfun (x + y) := wc_293 (x + y) (by linarith) (by linarith)
                      have hw4 : (14329561/5000000000000:ℝ) ≤ wfun (y + z) := wc_270 (y + z) (by linarith) (by linarith)
                      have hw5 : (1157601093/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_604 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · rcases le_total x (4267/4096:ℝ) with hc | hc
                    · rcases le_total y (8149/4096:ℝ) with hc | hc
                      · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                        have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_126 y (by linarith) (by linarith)
                        have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                        have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_284 (x + y) (by linarith) (by linarith)
                        have hw4 : (28027757/5000000000000:ℝ) ≤ wfun (y + z) := wc_285 (y + z) (by linarith) (by linarith)
                        have hw5 : (242372143/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_608 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                        have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
                        have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                        have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_292 (x + y) (by linarith) (by linarith)
                        have hw4 : (18276411/2500000000000:ℝ) ≤ wfun (y + z) := wc_293 (y + z) (by linarith) (by linarith)
                        have hw5 : (1265836939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_621 (x + y + z) (by linarith) (by linarith)
                        linarith
                    · rcases le_total y (8149/4096:ℝ) with hc | hc
                      · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                        have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_126 y (by linarith) (by linarith)
                        have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                        have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_292 (x + y) (by linarith) (by linarith)
                        have hw4 : (28027757/5000000000000:ℝ) ≤ wfun (y + z) := wc_285 (y + z) (by linarith) (by linarith)
                        have hw5 : (1265836939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_621 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                        have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
                        have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                        have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_298 (x + y) (by linarith) (by linarith)
                        have hw4 : (18276411/2500000000000:ℝ) ≤ wfun (y + z) := wc_293 (y + z) (by linarith) (by linarith)
                        have hw5 : (660458559/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_629 (x + y + z) (by linarith) (by linarith)
                        linarith
                · rcases le_total z (2131/2048:ℝ) with hc | hc
                  · rcases le_total x (4267/4096:ℝ) with hc | hc
                    · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                      have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_133 y (by linarith) (by linarith)
                      have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
                      have hw3 : (5774823/625000000000:ℝ) ≤ wfun (x + y) := wc_299 (x + y) (by linarith) (by linarith)
                      have hw4 : (55964847/10000000000000:ℝ) ≤ wfun (y + z) := wc_286 (y + z) (by linarith) (by linarith)
                      have hw5 : (121040499/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_609 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                      have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_133 y (by linarith) (by linarith)
                      have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
                      have hw3 : (569617/50000000000:ℝ) ≤ wfun (x + y) := wc_316 (x + y) (by linarith) (by linarith)
                      have hw4 : (55964847/10000000000000:ℝ) ≤ wfun (y + z) := wc_286 (y + z) (by linarith) (by linarith)
                      have hw5 : (1264316833/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_622 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · rcases le_total x (4267/4096:ℝ) with hc | hc
                    · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                      have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_133 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                      have hw3 : (5774823/625000000000:ℝ) ≤ wfun (x + y) := wc_299 (x + y) (by linarith) (by linarith)
                      have hw4 : (92247841/10000000000000:ℝ) ≤ wfun (y + z) := wc_300 (y + z) (by linarith) (by linarith)
                      have hw5 : (659665673/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_630 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · rcases le_total y (8159/4096:ℝ) with hc | hc
                      · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                        have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_132 y (by linarith) (by linarith)
                        have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                        have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_315 (x + y) (by linarith) (by linarith)
                        have hw4 : (5774823/625000000000:ℝ) ≤ wfun (y + z) := wc_299 (y + z) (by linarith) (by linarith)
                        have hw5 : (172136989/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_639 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                        have hw1 : (1245909663/5000000000000:ℝ) ≤ wfun y := wc_134 y (by linarith) (by linarith)
                        have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                        have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_318 (x + y) (by linarith) (by linarith)
                        have hw4 : (569617/50000000000:ℝ) ≤ wfun (y + z) := wc_316 (y + z) (by linarith) (by linarith)
                        have hw5 : (57374717/400000000000:ℝ) ≤ wfun (x + y + z) := wc_646 (x + y + z) (by linarith) (by linarith)
                        linarith
          · rcases le_total z (1063/1024:ℝ) with hc | hc
            · rcases le_total x (2131/2048:ℝ) with hc | hc
              · rcases le_total y (4087/2048:ℝ) with hc | hc
                · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
                  have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_135 y (by linarith) (by linarith)
                  have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
                  have hw3 : (92247841/10000000000000:ℝ) ≤ wfun (x + y) := wc_300 (x + y) (by linarith) (by linarith)
                  have hw4 : (7141617/2500000000000:ℝ) ≤ wfun (y + z) := wc_271 (y + z) (by linarith) (by linarith)
                  have hw5 : (200453243/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_582 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
                  have hw1 : (1868712167/10000000000000:ℝ) ≤ wfun y := wc_137 y (by linarith) (by linarith)
                  have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
                  have hw3 : (13745521/1000000000000:ℝ) ≤ wfun (x + y) := wc_320 (x + y) (by linarith) (by linarith)
                  have hw4 : (27892031/5000000000000:ℝ) ≤ wfun (y + z) := wc_287 (y + z) (by linarith) (by linarith)
                  have hw5 : (55096489/500000000000:ℝ) ≤ wfun (x + y + z) := wc_598 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (4087/2048:ℝ) with hc | hc
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
                  have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_135 y (by linarith) (by linarith)
                  have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
                  have hw3 : (13745521/1000000000000:ℝ) ≤ wfun (x + y) := wc_320 (x + y) (by linarith) (by linarith)
                  have hw4 : (7141617/2500000000000:ℝ) ≤ wfun (y + z) := wc_271 (y + z) (by linarith) (by linarith)
                  have hw5 : (55096489/500000000000:ℝ) ≤ wfun (x + y + z) := wc_598 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
                  have hw1 : (1868712167/10000000000000:ℝ) ≤ wfun y := wc_137 y (by linarith) (by linarith)
                  have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
                  have hw3 : (23941523/1250000000000:ℝ) ≤ wfun (x + y) := wc_326 (x + y) (by linarith) (by linarith)
                  have hw4 : (27892031/5000000000000:ℝ) ≤ wfun (y + z) := wc_287 (y + z) (by linarith) (by linarith)
                  have hw5 : (1206050917/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_611 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total x (2131/2048:ℝ) with hc | hc
              · rcases le_total y (4087/2048:ℝ) with hc | hc
                · rcases le_total z (2131/2048:ℝ) with hc | hc
                  · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
                    have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_135 y (by linarith) (by linarith)
                    have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
                    have hw3 : (92247841/10000000000000:ℝ) ≤ wfun (x + y) := wc_300 (x + y) (by linarith) (by linarith)
                    have hw4 : (92247841/10000000000000:ℝ) ≤ wfun (y + z) := wc_300 (y + z) (by linarith) (by linarith)
                    have hw5 : (1208951451/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_610 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
                    have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_135 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                    have hw3 : (92247841/10000000000000:ℝ) ≤ wfun (x + y) := wc_300 (x + y) (by linarith) (by linarith)
                    have hw4 : (13745521/1000000000000:ℝ) ≤ wfun (y + z) := wc_320 (y + z) (by linarith) (by linarith)
                    have hw5 : (263549591/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_631 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total z (2131/2048:ℝ) with hc | hc
                  · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
                    have hw1 : (1868712167/10000000000000:ℝ) ≤ wfun y := wc_137 y (by linarith) (by linarith)
                    have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
                    have hw3 : (13745521/1000000000000:ℝ) ≤ wfun (x + y) := wc_320 (x + y) (by linarith) (by linarith)
                    have hw4 : (13745521/1000000000000:ℝ) ≤ wfun (y + z) := wc_320 (y + z) (by linarith) (by linarith)
                    have hw5 : (263549591/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_631 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
                    have hw1 : (1868712167/10000000000000:ℝ) ≤ wfun y := wc_137 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                    have hw3 : (13745521/1000000000000:ℝ) ≤ wfun (x + y) := wc_320 (x + y) (by linarith) (by linarith)
                    have hw4 : (23941523/1250000000000:ℝ) ≤ wfun (y + z) := wc_326 (y + z) (by linarith) (by linarith)
                    have hw5 : (715464319/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_648 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total y (4087/2048:ℝ) with hc | hc
                · rcases le_total z (2131/2048:ℝ) with hc | hc
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
                    have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_135 y (by linarith) (by linarith)
                    have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
                    have hw3 : (13745521/1000000000000:ℝ) ≤ wfun (x + y) := wc_320 (x + y) (by linarith) (by linarith)
                    have hw4 : (92247841/10000000000000:ℝ) ≤ wfun (y + z) := wc_300 (y + z) (by linarith) (by linarith)
                    have hw5 : (263549591/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_631 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · rcases le_total x (4267/4096:ℝ) with hc | hc
                    · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                      have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_135 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                      have hw3 : (4302423/312500000000:ℝ) ≤ wfun (x + y) := wc_319 (x + y) (by linarith) (by linarith)
                      have hw4 : (13745521/1000000000000:ℝ) ≤ wfun (y + z) := wc_320 (y + z) (by linarith) (by linarith)
                      have hw5 : (1432646991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_647 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                      have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_135 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                      have hw3 : (163652657/10000000000000:ℝ) ≤ wfun (x + y) := wc_323 (x + y) (by linarith) (by linarith)
                      have hw4 : (13745521/1000000000000:ℝ) ≤ wfun (y + z) := wc_320 (y + z) (by linarith) (by linarith)
                      have hw5 : (298187457/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_666 (x + y + z) (by linarith) (by linarith)
                      linarith
                · rcases le_total z (2131/2048:ℝ) with hc | hc
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
                    have hw1 : (1868712167/10000000000000:ℝ) ≤ wfun y := wc_137 y (by linarith) (by linarith)
                    have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
                    have hw3 : (23941523/1250000000000:ℝ) ≤ wfun (x + y) := wc_326 (x + y) (by linarith) (by linarith)
                    have hw4 : (13745521/1000000000000:ℝ) ≤ wfun (y + z) := wc_320 (y + z) (by linarith) (by linarith)
                    have hw5 : (715464319/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_648 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
                    have hw1 : (1868712167/10000000000000:ℝ) ≤ wfun y := wc_137 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                    have hw3 : (23941523/1250000000000:ℝ) ≤ wfun (x + y) := wc_326 (x + y) (by linarith) (by linarith)
                    have hw4 : (23941523/1250000000000:ℝ) ≤ wfun (y + z) := wc_326 (y + z) (by linarith) (by linarith)
                    have hw5 : (1548450213/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_674 (x + y + z) (by linarith) (by linarith)
                    linarith
    · rcases le_total z (529/512:ℝ) with hc | hc
      · rcases le_total x (1063/1024:ℝ) with hc | hc
        · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_16 x (by linarith) (by linarith)
          have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
            rcases le_total y (2:ℝ) with hq10 | hq10
            · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
          have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
          have hw3 : (91064031/10000000000000:ℝ) ≤ wfun (x + y) := wc_303 (x + y) (by linarith) (by linarith)
          have hw4 : (231767/2000000000000:ℝ) ≤ wfun (y + z) := wc_246 (y + z) (by linarith) (by linarith)
          have hw5 : (79960111/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_547 (x + y + z) (by linarith) (by linarith)
          linarith
        · rcases le_total y (2051/1024:ℝ) with hc | hc
          · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
            have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
              rcases le_total y (2:ℝ) with hq10 | hq10
              · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_140 y (by linarith) (by linarith))
            have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
            have hw3 : (190300253/10000000000000:ℝ) ≤ wfun (x + y) := wc_328 (x + y) (by linarith) (by linarith)
            have hw4 : (1166349/10000000000000:ℝ) ≤ wfun (y + z) := wc_245 (y + z) (by linarith) (by linarith)
            have hw5 : (808657969/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_564 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
            have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
            have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
            have hw3 : (161986357/5000000000000:ℝ) ≤ wfun (x + y) := wc_342 (x + y) (by linarith) (by linarith)
            have hw4 : (28290747/10000000000000:ℝ) ≤ wfun (y + z) := wc_273 (y + z) (by linarith) (by linarith)
            have hw5 : (198537007/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_585 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total x (1063/1024:ℝ) with hc | hc
        · rcases le_total y (2051/1024:ℝ) with hc | hc
          · rcases le_total z (1063/1024:ℝ) with hc | hc
            · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_16 x (by linarith) (by linarith)
              have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
                rcases le_total y (2:ℝ) with hq10 | hq10
                · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_140 y (by linarith) (by linarith))
              have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
              have hw3 : (11456693/1250000000000:ℝ) ≤ wfun (x + y) := wc_302 (x + y) (by linarith) (by linarith)
              have hw4 : (11456693/1250000000000:ℝ) ≤ wfun (y + z) := wc_302 (y + z) (by linarith) (by linarith)
              have hw5 : (249365309/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_584 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (2121/2048:ℝ) with hc | hc
              · have hw0 : (1888462017/5000000000000:ℝ) ≤ wfun x := wc_15 x (by linarith) (by linarith)
                have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (2:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_140 y (by linarith) (by linarith))
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
                have hw3 : (22987523/2500000000000:ℝ) ≤ wfun (x + y) := wc_301 (x + y) (by linarith) (by linarith)
                have hw4 : (190300253/10000000000000:ℝ) ≤ wfun (y + z) := wc_328 (y + z) (by linarith) (by linarith)
                have hw5 : (1203159081/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_612 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
                have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (2:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_140 y (by linarith) (by linarith))
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
                have hw3 : (2140811/156250000000:ℝ) ≤ wfun (x + y) := wc_321 (x + y) (by linarith) (by linarith)
                have hw4 : (190300253/10000000000000:ℝ) ≤ wfun (y + z) := wc_328 (y + z) (by linarith) (by linarith)
                have hw5 : (655719053/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_633 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (1063/1024:ℝ) with hc | hc
            · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_16 x (by linarith) (by linarith)
              have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
              have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
              have hw3 : (190300253/10000000000000:ℝ) ≤ wfun (x + y) := wc_328 (x + y) (by linarith) (by linarith)
              have hw4 : (190300253/10000000000000:ℝ) ≤ wfun (y + z) := wc_328 (y + z) (by linarith) (by linarith)
              have hw5 : (600137957/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_613 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_16 x (by linarith) (by linarith)
              have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
              have hw3 : (190300253/10000000000000:ℝ) ≤ wfun (x + y) := wc_328 (x + y) (by linarith) (by linarith)
              have hw4 : (161986357/5000000000000:ℝ) ≤ wfun (y + z) := wc_342 (y + z) (by linarith) (by linarith)
              have hw5 : (1420672477/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_651 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (2051/1024:ℝ) with hc | hc
          · rcases le_total z (1063/1024:ℝ) with hc | hc
            · rcases le_total x (2131/2048:ℝ) with hc | hc
              · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
                have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (2:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_140 y (by linarith) (by linarith))
                have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
                have hw3 : (7636599/400000000000:ℝ) ≤ wfun (x + y) := wc_327 (x + y) (by linarith) (by linarith)
                have hw4 : (11456693/1250000000000:ℝ) ≤ wfun (y + z) := wc_302 (y + z) (by linarith) (by linarith)
                have hw5 : (1203159081/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_612 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
                have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (2:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_140 y (by linarith) (by linarith))
                have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
                have hw3 : (63400731/2500000000000:ℝ) ≤ wfun (x + y) := wc_335 (x + y) (by linarith) (by linarith)
                have hw4 : (11456693/1250000000000:ℝ) ≤ wfun (y + z) := wc_302 (y + z) (by linarith) (by linarith)
                have hw5 : (655719053/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_633 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (2131/2048:ℝ) with hc | hc
              · rcases le_total y (4097/2048:ℝ) with hc | hc
                · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
                  have hw1 : (1591808227/10000000000000:ℝ) ≤ wfun y := by
                    rcases le_total y (2:ℝ) with hq10 | hq10
                    · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_139 y (by linarith) (by linarith))
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
                  have hw3 : (23941523/1250000000000:ℝ) ≤ wfun (x + y) := wc_326 (x + y) (by linarith) (by linarith)
                  have hw4 : (7636599/400000000000:ℝ) ≤ wfun (y + z) := wc_327 (y + z) (by linarith) (by linarith)
                  have hw5 : (1427499659/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_649 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
                  have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
                  have hw3 : (25442213/1000000000000:ℝ) ≤ wfun (x + y) := wc_334 (x + y) (by linarith) (by linarith)
                  have hw4 : (63400731/2500000000000:ℝ) ≤ wfun (y + z) := wc_335 (y + z) (by linarith) (by linarith)
                  have hw5 : (1544741841/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_675 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (4097/2048:ℝ) with hc | hc
                · rcases le_total z (2131/2048:ℝ) with hc | hc
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
                    have hw1 : (1591808227/10000000000000:ℝ) ≤ wfun y := by
                      rcases le_total y (2:ℝ) with hq10 | hq10
                      · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_139 y (by linarith) (by linarith))
                    have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
                    have hw3 : (25442213/1000000000000:ℝ) ≤ wfun (x + y) := wc_334 (x + y) (by linarith) (by linarith)
                    have hw4 : (23941523/1250000000000:ℝ) ≤ wfun (y + z) := wc_326 (y + z) (by linarith) (by linarith)
                    have hw5 : (1548450213/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_674 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
                    have hw1 : (1591808227/10000000000000:ℝ) ≤ wfun y := by
                      rcases le_total y (2:ℝ) with hq10 | hq10
                      · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_139 y (by linarith) (by linarith))
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                    have hw3 : (25442213/1000000000000:ℝ) ≤ wfun (x + y) := wc_334 (x + y) (by linarith) (by linarith)
                    have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_334 (y + z) (by linarith) (by linarith)
                    have hw5 : (1670268489/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_688 (x + y + z) (by linarith) (by linarith)
                    linarith
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
                  have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
                  have hw3 : (326066581/10000000000000:ℝ) ≤ wfun (x + y) := wc_340 (x + y) (by linarith) (by linarith)
                  have hw4 : (63400731/2500000000000:ℝ) ≤ wfun (y + z) := wc_335 (y + z) (by linarith) (by linarith)
                  have hw5 : (1666270777/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_689 (x + y + z) (by linarith) (by linarith)
                  linarith
          · rcases le_total z (1063/1024:ℝ) with hc | hc
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
              have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
              have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
              have hw3 : (161986357/5000000000000:ℝ) ≤ wfun (x + y) := wc_342 (x + y) (by linarith) (by linarith)
              have hw4 : (190300253/10000000000000:ℝ) ≤ wfun (y + z) := wc_328 (y + z) (by linarith) (by linarith)
              have hw5 : (1420672477/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_651 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (2131/2048:ℝ) with hc | hc
              · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
                have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
                have hw3 : (325017537/10000000000000:ℝ) ≤ wfun (x + y) := wc_341 (x + y) (by linarith) (by linarith)
                have hw4 : (161986357/5000000000000:ℝ) ≤ wfun (y + z) := wc_342 (y + z) (by linarith) (by linarith)
                have hw5 : (66491401/400000000000:ℝ) ≤ wfun (x + y + z) := wc_690 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
                have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
                have hw3 : (405098789/10000000000000:ℝ) ≤ wfun (x + y) := wc_347 (x + y) (by linarith) (by linarith)
                have hw4 : (161986357/5000000000000:ℝ) ≤ wfun (y + z) := wc_342 (y + z) (by linarith) (by linarith)
                have hw5 : (1787757479/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_704 (x + y + z) (by linarith) (by linarith)
                linarith

set_option maxHeartbeats 20000000 in
lemma ch_20 (x y z : ℝ) (hx1 : (1073/1024:ℝ) ≤ x) (hx2 : x ≤ (539/512:ℝ))
    (hy1 : (1013/512:ℝ) ≤ y) (hy2 : y ≤ (509/256:ℝ))
    (hz1 : (529/512:ℝ) ≤ z) (hz2 : z ≤ (267/256:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total y (2031/1024:ℝ) with hc | hc
  · rcases le_total z (1063/1024:ℝ) with hc | hc
    · rcases le_total x (2151/2048:ℝ) with hc | hc
      · rcases le_total y (4057/2048:ℝ) with hc | hc
        · rcases le_total z (2121/2048:ℝ) with hc | hc
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
            have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_103 y (by linarith) (by linarith)
            have hw2 : (1888462017/5000000000000:ℝ) ≤ wfun z := wc_15 z (by linarith) (by linarith)
            have hw3 : (14329561/5000000000000:ℝ) ≤ wfun (x + y) := wc_270 (x + y) (by linarith) (by linarith)
            have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_231 (y + z) (by linarith) (by linarith)
            have hw5 : (12788137/156250000000:ℝ) ≤ wfun (x + y + z) := wc_560 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
            have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_103 y (by linarith) (by linarith)
            have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
            have hw3 : (14329561/5000000000000:ℝ) ≤ wfun (x + y) := wc_270 (x + y) (by linarith) (by linarith)
            have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_234 (y + z) (by linarith) (by linarith)
            have hw5 : (56830383/625000000000:ℝ) ≤ wfun (x + y + z) := wc_571 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (2121/2048:ℝ) with hc | hc
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
            have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_112 y (by linarith) (by linarith)
            have hw2 : (1888462017/5000000000000:ℝ) ≤ wfun z := wc_15 z (by linarith) (by linarith)
            have hw3 : (55964847/10000000000000:ℝ) ≤ wfun (x + y) := wc_286 (x + y) (by linarith) (by linarith)
            have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_234 (y + z) (by linarith) (by linarith)
            have hw5 : (56830383/625000000000:ℝ) ≤ wfun (x + y + z) := wc_571 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
            have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_112 y (by linarith) (by linarith)
            have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
            have hw3 : (55964847/10000000000000:ℝ) ≤ wfun (x + y) := wc_286 (x + y) (by linarith) (by linarith)
            have hw5 : (1004679561/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_581 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total y (4057/2048:ℝ) with hc | hc
        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
          have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_103 y (by linarith) (by linarith)
          have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
          have hw3 : (55964847/10000000000000:ℝ) ≤ wfun (x + y) := wc_286 (x + y) (by linarith) (by linarith)
          have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_232 (y + z) (by linarith) (by linarith)
          have hw5 : (907100611/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_572 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
          have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_112 y (by linarith) (by linarith)
          have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
          have hw3 : (92247841/10000000000000:ℝ) ≤ wfun (x + y) := wc_300 (x + y) (by linarith) (by linarith)
          have hw5 : (200453243/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_582 (x + y + z) (by linarith) (by linarith)
          linarith
    · rcases le_total x (2151/2048:ℝ) with hc | hc
      · rcases le_total y (4057/2048:ℝ) with hc | hc
        · rcases le_total z (2131/2048:ℝ) with hc | hc
          · rcases le_total x (4297/4096:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
              have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_103 y (by linarith) (by linarith)
              have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
              have hw3 : (2870559/1000000000000:ℝ) ≤ wfun (x + y) := wc_269 (x + y) (by linarith) (by linarith)
              have hw5 : (1005888959/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_580 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
              have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_103 y (by linarith) (by linarith)
              have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
              have hw3 : (20626673/5000000000000:ℝ) ≤ wfun (x + y) := wc_279 (x + y) (by linarith) (by linarith)
              have hw5 : (1055337947/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_592 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (4297/4096:ℝ) with hc | hc
            · rcases le_total y (8109/4096:ℝ) with hc | hc
              · rcases le_total z (4267/4096:ℝ) with hc | hc
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                  have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
                  have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_23 z (by linarith) (by linarith)
                  have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_268 (x + y) (by linarith) (by linarith)
                  have hw5 : (1108574073/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_594 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                  have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
                  have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_268 (x + y) (by linarith) (by linarith)
                  have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_237 (y + z) (by linarith) (by linarith)
                  have hw5 : (290097117/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_602 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (4267/4096:ℝ) with hc | hc
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                  have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
                  have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_23 z (by linarith) (by linarith)
                  have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_278 (x + y) (by linarith) (by linarith)
                  have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_237 (y + z) (by linarith) (by linarith)
                  have hw5 : (290097117/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_602 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                  have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
                  have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_278 (x + y) (by linarith) (by linarith)
                  have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_240 (y + z) (by linarith) (by linarith)
                  have hw5 : (1213318631/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_607 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total y (8109/4096:ℝ) with hc | hc
              · rcases le_total z (4267/4096:ℝ) with hc | hc
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                  have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
                  have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_23 z (by linarith) (by linarith)
                  have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_278 (x + y) (by linarith) (by linarith)
                  have hw5 : (290097117/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_602 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                  have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
                  have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_278 (x + y) (by linarith) (by linarith)
                  have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_237 (y + z) (by linarith) (by linarith)
                  have hw5 : (1213318631/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_607 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (4267/4096:ℝ) with hc | hc
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                  have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
                  have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_23 z (by linarith) (by linarith)
                  have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_284 (x + y) (by linarith) (by linarith)
                  have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_237 (y + z) (by linarith) (by linarith)
                  have hw5 : (1213318631/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_607 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                  have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
                  have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_284 (x + y) (by linarith) (by linarith)
                  have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_240 (y + z) (by linarith) (by linarith)
                  have hw5 : (1267359331/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_620 (x + y + z) (by linarith) (by linarith)
                  linarith
        · rcases le_total z (2131/2048:ℝ) with hc | hc
          · rcases le_total x (4297/4096:ℝ) with hc | hc
            · rcases le_total y (8119/4096:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
                have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
                have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_284 (x + y) (by linarith) (by linarith)
                have hw5 : (553620607/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_595 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
                have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
                have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_292 (x + y) (by linarith) (by linarith)
                have hw4 : (41/1250000000000:ℝ) ≤ wfun (y + z) := wc_238 (y + z) (by linarith) (by linarith)
                have hw5 : (1158993733/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_603 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (8119/4096:ℝ) with hc | hc
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
                have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
                have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_292 (x + y) (by linarith) (by linarith)
                have hw5 : (1158993733/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_603 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
                have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
                have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_298 (x + y) (by linarith) (by linarith)
                have hw4 : (41/1250000000000:ℝ) ≤ wfun (y + z) := wc_238 (y + z) (by linarith) (by linarith)
                have hw5 : (242372143/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_608 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (4297/4096:ℝ) with hc | hc
            · rcases le_total y (8119/4096:ℝ) with hc | hc
              · rcases le_total z (4267/4096:ℝ) with hc | hc
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                  have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
                  have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_23 z (by linarith) (by linarith)
                  have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_284 (x + y) (by linarith) (by linarith)
                  have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_240 (y + z) (by linarith) (by linarith)
                  have hw5 : (1213318631/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_607 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                  have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
                  have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_284 (x + y) (by linarith) (by linarith)
                  have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_250 (y + z) (by linarith) (by linarith)
                  have hw5 : (1267359331/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_620 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (4267/4096:ℝ) with hc | hc
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                  have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
                  have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_23 z (by linarith) (by linarith)
                  have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_292 (x + y) (by linarith) (by linarith)
                  have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_250 (y + z) (by linarith) (by linarith)
                  have hw5 : (1267359331/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_620 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                  have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
                  have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_292 (x + y) (by linarith) (by linarith)
                  have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
                  have hw5 : (52900211/400000000000:ℝ) ≤ wfun (x + y + z) := wc_628 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total y (8119/4096:ℝ) with hc | hc
              · rcases le_total z (4267/4096:ℝ) with hc | hc
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                  have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
                  have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_23 z (by linarith) (by linarith)
                  have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_292 (x + y) (by linarith) (by linarith)
                  have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_240 (y + z) (by linarith) (by linarith)
                  have hw5 : (1267359331/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_620 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                  have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
                  have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_292 (x + y) (by linarith) (by linarith)
                  have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_250 (y + z) (by linarith) (by linarith)
                  have hw5 : (52900211/400000000000:ℝ) ≤ wfun (x + y + z) := wc_628 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (4267/4096:ℝ) with hc | hc
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                  have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
                  have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_23 z (by linarith) (by linarith)
                  have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_298 (x + y) (by linarith) (by linarith)
                  have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_250 (y + z) (by linarith) (by linarith)
                  have hw5 : (52900211/400000000000:ℝ) ≤ wfun (x + y + z) := wc_628 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                  have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
                  have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_298 (x + y) (by linarith) (by linarith)
                  have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
                  have hw5 : (275750223/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_638 (x + y + z) (by linarith) (by linarith)
                  linarith
      · rcases le_total y (4057/2048:ℝ) with hc | hc
        · rcases le_total z (2131/2048:ℝ) with hc | hc
          · rcases le_total x (4307/4096:ℝ) with hc | hc
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_103 y (by linarith) (by linarith)
              have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
              have hw3 : (28027757/5000000000000:ℝ) ≤ wfun (x + y) := wc_285 (x + y) (by linarith) (by linarith)
              have hw5 : (1105910359/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_596 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_103 y (by linarith) (by linarith)
              have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
              have hw3 : (18276411/2500000000000:ℝ) ≤ wfun (x + y) := wc_293 (x + y) (by linarith) (by linarith)
              have hw5 : (1157601093/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_604 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (4307/4096:ℝ) with hc | hc
            · rcases le_total y (8109/4096:ℝ) with hc | hc
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_284 (x + y) (by linarith) (by linarith)
                have hw5 : (242372143/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_608 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_292 (x + y) (by linarith) (by linarith)
                have hw4 : (41/1250000000000:ℝ) ≤ wfun (y + z) := wc_238 (y + z) (by linarith) (by linarith)
                have hw5 : (1265836939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_621 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (8109/4096:ℝ) with hc | hc
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_292 (x + y) (by linarith) (by linarith)
                have hw5 : (1265836939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_621 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_298 (x + y) (by linarith) (by linarith)
                have hw4 : (41/1250000000000:ℝ) ≤ wfun (y + z) := wc_238 (y + z) (by linarith) (by linarith)
                have hw5 : (660458559/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_629 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (2131/2048:ℝ) with hc | hc
          · rcases le_total x (4307/4096:ℝ) with hc | hc
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_112 y (by linarith) (by linarith)
              have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
              have hw3 : (5774823/625000000000:ℝ) ≤ wfun (x + y) := wc_299 (x + y) (by linarith) (by linarith)
              have hw5 : (121040499/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_609 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_112 y (by linarith) (by linarith)
              have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
              have hw3 : (569617/50000000000:ℝ) ≤ wfun (x + y) := wc_316 (x + y) (by linarith) (by linarith)
              have hw5 : (1264316833/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_622 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (4307/4096:ℝ) with hc | hc
            · rcases le_total y (8119/4096:ℝ) with hc | hc
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_298 (x + y) (by linarith) (by linarith)
                have hw4 : (29587/250000000000:ℝ) ≤ wfun (y + z) := wc_241 (y + z) (by linarith) (by linarith)
                have hw5 : (660458559/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_629 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total z (4267/4096:ℝ) with hc | hc
                · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                  have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
                  have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_23 z (by linarith) (by linarith)
                  have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_315 (x + y) (by linarith) (by linarith)
                  have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_250 (y + z) (by linarith) (by linarith)
                  have hw5 : (275750223/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_638 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                  have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
                  have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_315 (x + y) (by linarith) (by linarith)
                  have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
                  have hw5 : (718045723/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_645 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total y (8119/4096:ℝ) with hc | hc
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_315 (x + y) (by linarith) (by linarith)
                have hw4 : (29587/250000000000:ℝ) ≤ wfun (y + z) := wc_241 (y + z) (by linarith) (by linarith)
                have hw5 : (172136989/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_639 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_318 (x + y) (by linarith) (by linarith)
                have hw4 : (465149/1000000000000:ℝ) ≤ wfun (y + z) := wc_251 (y + z) (by linarith) (by linarith)
                have hw5 : (57374717/400000000000:ℝ) ≤ wfun (x + y + z) := wc_646 (x + y + z) (by linarith) (by linarith)
                linarith
  · rcases le_total z (1063/1024:ℝ) with hc | hc
    · rcases le_total x (2151/2048:ℝ) with hc | hc
      · rcases le_total y (4067/2048:ℝ) with hc | hc
        · rcases le_total z (2121/2048:ℝ) with hc | hc
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
            have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_119 y (by linarith) (by linarith)
            have hw2 : (1888462017/5000000000000:ℝ) ≤ wfun z := wc_15 z (by linarith) (by linarith)
            have hw3 : (92247841/10000000000000:ℝ) ≤ wfun (x + y) := wc_300 (x + y) (by linarith) (by linarith)
            have hw5 : (1004679561/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_581 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
            have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_119 y (by linarith) (by linarith)
            have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
            have hw3 : (92247841/10000000000000:ℝ) ≤ wfun (x + y) := wc_300 (x + y) (by linarith) (by linarith)
            have hw5 : (8629543/78125000000:ℝ) ≤ wfun (x + y + z) := wc_597 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (2121/2048:ℝ) with hc | hc
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
            have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
            have hw2 : (1888462017/5000000000000:ℝ) ≤ wfun z := wc_15 z (by linarith) (by linarith)
            have hw3 : (13745521/1000000000000:ℝ) ≤ wfun (x + y) := wc_320 (x + y) (by linarith) (by linarith)
            have hw5 : (8629543/78125000000:ℝ) ≤ wfun (x + y + z) := wc_597 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
            have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
            have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
            have hw3 : (13745521/1000000000000:ℝ) ≤ wfun (x + y) := wc_320 (x + y) (by linarith) (by linarith)
            have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_242 (y + z) (by linarith) (by linarith)
            have hw5 : (1208951451/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_610 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total y (4067/2048:ℝ) with hc | hc
        · rcases le_total z (2121/2048:ℝ) with hc | hc
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
            have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_119 y (by linarith) (by linarith)
            have hw2 : (1888462017/5000000000000:ℝ) ≤ wfun z := wc_15 z (by linarith) (by linarith)
            have hw3 : (13745521/1000000000000:ℝ) ≤ wfun (x + y) := wc_320 (x + y) (by linarith) (by linarith)
            have hw5 : (8629543/78125000000:ℝ) ≤ wfun (x + y + z) := wc_597 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
            have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_119 y (by linarith) (by linarith)
            have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
            have hw3 : (13745521/1000000000000:ℝ) ≤ wfun (x + y) := wc_320 (x + y) (by linarith) (by linarith)
            have hw5 : (1208951451/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_610 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (2121/2048:ℝ) with hc | hc
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
            have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
            have hw2 : (1888462017/5000000000000:ℝ) ≤ wfun z := wc_15 z (by linarith) (by linarith)
            have hw3 : (23941523/1250000000000:ℝ) ≤ wfun (x + y) := wc_326 (x + y) (by linarith) (by linarith)
            have hw5 : (1208951451/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_610 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
            have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
            have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
            have hw3 : (23941523/1250000000000:ℝ) ≤ wfun (x + y) := wc_326 (x + y) (by linarith) (by linarith)
            have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_242 (y + z) (by linarith) (by linarith)
            have hw5 : (263549591/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_631 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total x (2151/2048:ℝ) with hc | hc
      · rcases le_total y (4067/2048:ℝ) with hc | hc
        · rcases le_total z (2131/2048:ℝ) with hc | hc
          · rcases le_total x (4297/4096:ℝ) with hc | hc
            · rcases le_total y (8129/4096:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
                have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
                have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_298 (x + y) (by linarith) (by linarith)
                have hw4 : (29587/250000000000:ℝ) ≤ wfun (y + z) := wc_241 (y + z) (by linarith) (by linarith)
                have hw5 : (242372143/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_608 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
                have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
                have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_315 (x + y) (by linarith) (by linarith)
                have hw4 : (465149/1000000000000:ℝ) ≤ wfun (y + z) := wc_251 (y + z) (by linarith) (by linarith)
                have hw5 : (1265836939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_621 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (8129/4096:ℝ) with hc | hc
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
                have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
                have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_315 (x + y) (by linarith) (by linarith)
                have hw4 : (29587/250000000000:ℝ) ≤ wfun (y + z) := wc_241 (y + z) (by linarith) (by linarith)
                have hw5 : (1265836939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_621 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
                have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
                have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_318 (x + y) (by linarith) (by linarith)
                have hw4 : (465149/1000000000000:ℝ) ≤ wfun (y + z) := wc_251 (y + z) (by linarith) (by linarith)
                have hw5 : (660458559/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_629 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (4297/4096:ℝ) with hc | hc
            · rcases le_total y (8129/4096:ℝ) with hc | hc
              · rcases le_total z (4267/4096:ℝ) with hc | hc
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                  have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
                  have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_23 z (by linarith) (by linarith)
                  have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_298 (x + y) (by linarith) (by linarith)
                  have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
                  have hw5 : (52900211/400000000000:ℝ) ≤ wfun (x + y + z) := wc_628 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                  have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
                  have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_298 (x + y) (by linarith) (by linarith)
                  have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_262 (y + z) (by linarith) (by linarith)
                  have hw5 : (275750223/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_638 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (4267/4096:ℝ) with hc | hc
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                  have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
                  have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_23 z (by linarith) (by linarith)
                  have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_315 (x + y) (by linarith) (by linarith)
                  have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_262 (y + z) (by linarith) (by linarith)
                  have hw5 : (275750223/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_638 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                  have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
                  have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_315 (x + y) (by linarith) (by linarith)
                  have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_268 (y + z) (by linarith) (by linarith)
                  have hw5 : (718045723/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_645 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total y (8129/4096:ℝ) with hc | hc
              · rcases le_total z (4267/4096:ℝ) with hc | hc
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                  have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
                  have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_23 z (by linarith) (by linarith)
                  have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_315 (x + y) (by linarith) (by linarith)
                  have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
                  have hw5 : (275750223/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_638 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                  have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
                  have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_315 (x + y) (by linarith) (by linarith)
                  have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_262 (y + z) (by linarith) (by linarith)
                  have hw5 : (718045723/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_645 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (4267/4096:ℝ) with hc | hc
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                  have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
                  have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_23 z (by linarith) (by linarith)
                  have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_318 (x + y) (by linarith) (by linarith)
                  have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_262 (y + z) (by linarith) (by linarith)
                  have hw5 : (718045723/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_645 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                  have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
                  have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_318 (x + y) (by linarith) (by linarith)
                  have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_268 (y + z) (by linarith) (by linarith)
                  have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_664 (x + y + z) (by linarith) (by linarith)
                  linarith
        · rcases le_total z (2131/2048:ℝ) with hc | hc
          · rcases le_total x (4297/4096:ℝ) with hc | hc
            · rcases le_total y (8139/4096:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
                have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
                have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_318 (x + y) (by linarith) (by linarith)
                have hw4 : (649907/625000000000:ℝ) ≤ wfun (y + z) := wc_255 (y + z) (by linarith) (by linarith)
                have hw5 : (660458559/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_629 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
                have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
                have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_322 (x + y) (by linarith) (by linarith)
                have hw4 : (736743/400000000000:ℝ) ≤ wfun (y + z) := wc_263 (y + z) (by linarith) (by linarith)
                have hw5 : (172136989/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_639 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
              have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
              have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
              have hw3 : (163652657/10000000000000:ℝ) ≤ wfun (x + y) := wc_323 (x + y) (by linarith) (by linarith)
              have hw4 : (2076333/2000000000000:ℝ) ≤ wfun (y + z) := wc_256 (y + z) (by linarith) (by linarith)
              have hw5 : (275088639/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_640 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (4297/4096:ℝ) with hc | hc
            · rcases le_total y (8139/4096:ℝ) with hc | hc
              · rcases le_total z (4267/4096:ℝ) with hc | hc
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                  have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
                  have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_23 z (by linarith) (by linarith)
                  have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_318 (x + y) (by linarith) (by linarith)
                  have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_268 (y + z) (by linarith) (by linarith)
                  have hw5 : (718045723/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_645 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                  have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
                  have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_318 (x + y) (by linarith) (by linarith)
                  have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
                  have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_664 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (4267/4096:ℝ) with hc | hc
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                  have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
                  have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_23 z (by linarith) (by linarith)
                  have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_322 (x + y) (by linarith) (by linarith)
                  have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
                  have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_664 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                  have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
                  have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_322 (x + y) (by linarith) (by linarith)
                  have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
                  have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_671 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total y (8139/4096:ℝ) with hc | hc
              · rcases le_total z (4267/4096:ℝ) with hc | hc
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                  have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
                  have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_23 z (by linarith) (by linarith)
                  have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_322 (x + y) (by linarith) (by linarith)
                  have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_268 (y + z) (by linarith) (by linarith)
                  have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_664 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                  have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
                  have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_322 (x + y) (by linarith) (by linarith)
                  have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
                  have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_671 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                have hw3 : (192151891/10000000000000:ℝ) ≤ wfun (x + y) := wc_324 (x + y) (by linarith) (by linarith)
                have hw4 : (20626673/5000000000000:ℝ) ≤ wfun (y + z) := wc_279 (y + z) (by linarith) (by linarith)
                have hw5 : (62086789/400000000000:ℝ) ≤ wfun (x + y + z) := wc_672 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total y (4067/2048:ℝ) with hc | hc
        · rcases le_total z (2131/2048:ℝ) with hc | hc
          · rcases le_total x (4307/4096:ℝ) with hc | hc
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_119 y (by linarith) (by linarith)
              have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
              have hw3 : (4302423/312500000000:ℝ) ≤ wfun (x + y) := wc_319 (x + y) (by linarith) (by linarith)
              have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_242 (y + z) (by linarith) (by linarith)
              have hw5 : (659665673/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_630 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_119 y (by linarith) (by linarith)
              have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
              have hw3 : (163652657/10000000000000:ℝ) ≤ wfun (x + y) := wc_323 (x + y) (by linarith) (by linarith)
              have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_242 (y + z) (by linarith) (by linarith)
              have hw5 : (275088639/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_640 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (4307/4096:ℝ) with hc | hc
            · rcases le_total y (8129/4096:ℝ) with hc | hc
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_318 (x + y) (by linarith) (by linarith)
                have hw4 : (649907/625000000000:ℝ) ≤ wfun (y + z) := wc_255 (y + z) (by linarith) (by linarith)
                have hw5 : (57374717/400000000000:ℝ) ≤ wfun (x + y + z) := wc_646 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_322 (x + y) (by linarith) (by linarith)
                have hw4 : (736743/400000000000:ℝ) ≤ wfun (y + z) := wc_263 (y + z) (by linarith) (by linarith)
                have hw5 : (1492727701/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_665 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (8129/4096:ℝ) with hc | hc
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_322 (x + y) (by linarith) (by linarith)
                have hw4 : (649907/625000000000:ℝ) ≤ wfun (y + z) := wc_255 (y + z) (by linarith) (by linarith)
                have hw5 : (1492727701/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_665 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                have hw3 : (192151891/10000000000000:ℝ) ≤ wfun (x + y) := wc_324 (x + y) (by linarith) (by linarith)
                have hw4 : (736743/400000000000:ℝ) ≤ wfun (y + z) := wc_263 (y + z) (by linarith) (by linarith)
                have hw5 : (62086789/400000000000:ℝ) ≤ wfun (x + y + z) := wc_672 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (2131/2048:ℝ) with hc | hc
          · rcases le_total x (4307/4096:ℝ) with hc | hc
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
              have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
              have hw3 : (47960431/2500000000000:ℝ) ≤ wfun (x + y) := wc_325 (x + y) (by linarith) (by linarith)
              have hw4 : (2076333/2000000000000:ℝ) ≤ wfun (y + z) := wc_256 (y + z) (by linarith) (by linarith)
              have hw5 : (1432646991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_647 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
              have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
              have hw3 : (111118793/5000000000000:ℝ) ≤ wfun (x + y) := wc_331 (x + y) (by linarith) (by linarith)
              have hw4 : (2076333/2000000000000:ℝ) ≤ wfun (y + z) := wc_256 (y + z) (by linarith) (by linarith)
              have hw5 : (298187457/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_666 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (4307/4096:ℝ) with hc | hc
            · rcases le_total y (8139/4096:ℝ) with hc | hc
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                have hw3 : (192151891/10000000000000:ℝ) ≤ wfun (x + y) := wc_324 (x + y) (by linarith) (by linarith)
                have hw4 : (2870559/1000000000000:ℝ) ≤ wfun (y + z) := wc_269 (y + z) (by linarith) (by linarith)
                have hw5 : (62086789/400000000000:ℝ) ≤ wfun (x + y + z) := wc_672 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                have hw3 : (890387/40000000000:ℝ) ≤ wfun (x + y) := wc_330 (x + y) (by linarith) (by linarith)
                have hw4 : (20626673/5000000000000:ℝ) ≤ wfun (y + z) := wc_279 (y + z) (by linarith) (by linarith)
                have hw5 : (322537687/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_681 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
              have hw3 : (111118793/5000000000000:ℝ) ≤ wfun (x + y) := wc_331 (x + y) (by linarith) (by linarith)
              have hw4 : (14329561/5000000000000:ℝ) ≤ wfun (y + z) := wc_270 (y + z) (by linarith) (by linarith)
              have hw5 : (1610755299/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_682 (x + y + z) (by linarith) (by linarith)
              linarith

set_option maxHeartbeats 20000000 in
lemma ch_41 (x y z : ℝ) (hx1 : (539/512:ℝ) ≤ x) (hx2 : x ≤ (17/16:ℝ))
    (hy1 : (509/256:ℝ) ≤ y) (hy2 : y ≤ (257/128:ℝ))
    (hz1 : (131/128:ℝ) ≤ z) (hz2 : z ≤ (267/256:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total y (1023/512:ℝ) with hc | hc
  · rcases le_total z (529/512:ℝ) with hc | hc
    · rcases le_total x (1083/1024:ℝ) with hc | hc
      · rcases le_total y (2041/1024:ℝ) with hc | hc
        · have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
          have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
          have hw3 : (161986357/5000000000000:ℝ) ≤ wfun (x + y) := wc_342 (x + y) (by linarith) (by linarith)
          have hw5 : (198537007/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_585 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
          have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
          have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_350 (x + y) (by linarith) (by linarith)
          have hw5 : (37329233/312500000000:ℝ) ≤ wfun (x + y + z) := wc_614 (x + y + z) (by linarith) (by linarith)
          linarith
      · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
        have hw1 : (1865845891/10000000000000:ℝ) ≤ wfun y := wc_129 y (by linarith) (by linarith)
        have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
        have hw3 : (489049523/10000000000000:ℝ) ≤ wfun (x + y) := wc_351 (x + y) (by linarith) (by linarith)
        have hw5 : (74301831/625000000000:ℝ) ≤ wfun (x + y + z) := wc_615 (x + y + z) (by linarith) (by linarith)
        linarith
    · rcases le_total x (1083/1024:ℝ) with hc | hc
      · rcases le_total y (2041/1024:ℝ) with hc | hc
        · rcases le_total z (1063/1024:ℝ) with hc | hc
          · rcases le_total x (2161/2048:ℝ) with hc | hc
            · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
              have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
              have hw3 : (325017537/10000000000000:ℝ) ≤ wfun (x + y) := wc_341 (x + y) (by linarith) (by linarith)
              have hw4 : (293481/2500000000000:ℝ) ≤ wfun (y + z) := wc_244 (y + z) (by linarith) (by linarith)
              have hw5 : (1424080951/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_650 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
              have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
              have hw3 : (405098789/10000000000000:ℝ) ≤ wfun (x + y) := wc_347 (x + y) (by linarith) (by linarith)
              have hw4 : (293481/2500000000000:ℝ) ≤ wfun (y + z) := wc_244 (y + z) (by linarith) (by linarith)
              have hw5 : (1541044571/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_676 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (2161/2048:ℝ) with hc | hc
            · rcases le_total y (4077/2048:ℝ) with hc | hc
              · rcases le_total z (2131/2048:ℝ) with hc | hc
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                  have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_127 y (by linarith) (by linarith)
                  have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
                  have hw3 : (326066581/10000000000000:ℝ) ≤ wfun (x + y) := wc_340 (x + y) (by linarith) (by linarith)
                  have hw4 : (14329561/5000000000000:ℝ) ≤ wfun (y + z) := wc_270 (y + z) (by linarith) (by linarith)
                  have hw5 : (1670268489/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_688 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                  have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_127 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                  have hw3 : (326066581/10000000000000:ℝ) ≤ wfun (x + y) := wc_340 (x + y) (by linarith) (by linarith)
                  have hw4 : (55964847/10000000000000:ℝ) ≤ wfun (y + z) := wc_286 (y + z) (by linarith) (by linarith)
                  have hw5 : (1796338383/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_702 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_133 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
                have hw3 : (406405247/10000000000000:ℝ) ≤ wfun (x + y) := wc_346 (x + y) (by linarith) (by linarith)
                have hw4 : (27892031/5000000000000:ℝ) ≤ wfun (y + z) := wc_287 (y + z) (by linarith) (by linarith)
                have hw5 : (1792041507/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_703 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (4077/2048:ℝ) with hc | hc
              · have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_127 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
                have hw3 : (406405247/10000000000000:ℝ) ≤ wfun (x + y) := wc_346 (x + y) (by linarith) (by linarith)
                have hw4 : (7141617/2500000000000:ℝ) ≤ wfun (y + z) := wc_271 (y + z) (by linarith) (by linarith)
                have hw5 : (1792041507/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_703 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_133 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
                have hw3 : (495376037/10000000000000:ℝ) ≤ wfun (x + y) := wc_348 (x + y) (by linarith) (by linarith)
                have hw4 : (27892031/5000000000000:ℝ) ≤ wfun (y + z) := wc_287 (y + z) (by linarith) (by linarith)
                have hw5 : (1922008203/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_711 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (1063/1024:ℝ) with hc | hc
          · have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
            have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
            have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_350 (x + y) (by linarith) (by linarith)
            have hw4 : (28474189/10000000000000:ℝ) ≤ wfun (y + z) := wc_272 (y + z) (by linarith) (by linarith)
            have hw5 : (1658311191/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_691 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (2161/2048:ℝ) with hc | hc
            · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
              have hw3 : (493784853/10000000000000:ℝ) ≤ wfun (x + y) := wc_349 (x + y) (by linarith) (by linarith)
              have hw4 : (11456693/1250000000000:ℝ) ≤ wfun (y + z) := wc_302 (y + z) (by linarith) (by linarith)
              have hw5 : (1917416231/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_712 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
              have hw3 : (295506067/5000000000000:ℝ) ≤ wfun (x + y) := wc_353 (x + y) (by linarith) (by linarith)
              have hw4 : (11456693/1250000000000:ℝ) ≤ wfun (y + z) := wc_302 (y + z) (by linarith) (by linarith)
              have hw5 : (410242943/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_724 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total y (2041/1024:ℝ) with hc | hc
        · rcases le_total z (1063/1024:ℝ) with hc | hc
          · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
            have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
            have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
            have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_350 (x + y) (by linarith) (by linarith)
            have hw4 : (293481/2500000000000:ℝ) ≤ wfun (y + z) := wc_244 (y + z) (by linarith) (by linarith)
            have hw5 : (1658311191/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_691 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
            have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
            have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
            have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_350 (x + y) (by linarith) (by linarith)
            have hw4 : (28474189/10000000000000:ℝ) ≤ wfun (y + z) := wc_272 (y + z) (by linarith) (by linarith)
            have hw5 : (1912837973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_713 (x + y + z) (by linarith) (by linarith)
            linarith
        · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
          have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
          have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
          have hw3 : (694482783/10000000000000:ℝ) ≤ wfun (x + y) := wc_354 (x + y) (by linarith) (by linarith)
          have hw4 : (28290747/10000000000000:ℝ) ≤ wfun (y + z) := wc_273 (y + z) (by linarith) (by linarith)
          have hw5 : (951861201/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_714 (x + y + z) (by linarith) (by linarith)
          linarith
  · rcases le_total z (529/512:ℝ) with hc | hc
    · have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
        rcases le_total y (2:ℝ) with hq10 | hq10
        · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
      have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
      have hw3 : (685641829/10000000000000:ℝ) ≤ wfun (x + y) := wc_356 (x + y) (by linarith) (by linarith)
      have hw4 : (231767/2000000000000:ℝ) ≤ wfun (y + z) := wc_246 (y + z) (by linarith) (by linarith)
      have hw5 : (140043451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_654 (x + y + z) (by linarith) (by linarith)
      linarith
    · rcases le_total x (1083/1024:ℝ) with hc | hc
      · rcases le_total y (2051/1024:ℝ) with hc | hc
        · rcases le_total z (1063/1024:ℝ) with hc | hc
          · have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
              rcases le_total y (2:ℝ) with hq10 | hq10
              · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_140 y (by linarith) (by linarith))
            have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
            have hw3 : (694482783/10000000000000:ℝ) ≤ wfun (x + y) := wc_354 (x + y) (by linarith) (by linarith)
            have hw4 : (11456693/1250000000000:ℝ) ≤ wfun (y + z) := wc_302 (y + z) (by linarith) (by linarith)
            have hw5 : (1912837973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_713 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
              rcases le_total y (2:ℝ) with hq10 | hq10
              · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_140 y (by linarith) (by linarith))
            have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
            have hw3 : (694482783/10000000000000:ℝ) ≤ wfun (x + y) := wc_354 (x + y) (by linarith) (by linarith)
            have hw4 : (190300253/10000000000000:ℝ) ≤ wfun (y + z) := wc_328 (y + z) (by linarith) (by linarith)
            have hw5 : (272985599/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_728 (x + y + z) (by linarith) (by linarith)
            linarith
        · have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
          have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
          have hw3 : (930293373/10000000000000:ℝ) ≤ wfun (x + y) := wc_362 (x + y) (by linarith) (by linarith)
          have hw4 : (189078223/10000000000000:ℝ) ≤ wfun (y + z) := wc_329 (y + z) (by linarith) (by linarith)
          have hw5 : (271686247/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_729 (x + y + z) (by linarith) (by linarith)
          linarith
      · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
        have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
          rcases le_total y (2:ℝ) with hq10 | hq10
          · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
        have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
        have hw3 : (924357731/10000000000000:ℝ) ≤ wfun (x + y) := wc_363 (x + y) (by linarith) (by linarith)
        have hw4 : (18095851/2000000000000:ℝ) ≤ wfun (y + z) := wc_304 (y + z) (by linarith) (by linarith)
        have hw5 : (216315697/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_730 (x + y + z) (by linarith) (by linarith)
        linarith

set_option maxHeartbeats 20000000 in
lemma ch_67 (x y z : ℝ) (hx1 : (63/64:ℝ) ≤ x) (hx2 : x ≤ (73/64:ℝ))
    (hy1 : (179/64:ℝ) ≤ y) (hy2 : y ≤ (105/32:ℝ))
    (hz1 : (121/64:ℝ) ≤ z) (hz2 : z ≤ (141/64:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total y (389/128:ℝ) with hc | hc
  · rcases le_total z (131/64:ℝ) with hc | hc
    · rcases le_total y (747/256:ℝ) with hc | hc
      · have hw1 : (1457053011/2000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
        have hw4 : (498772193/10000000000000:ℝ) ≤ wfun (y + z) := by
          rcases le_total (y + z) (19/4:ℝ) with hq40 | hq40
          · exact le_trans (by norm_num) (wc_761 (y + z) (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_762 (y + z) (by linarith) (by linarith))
        linarith
      · linarith
    · linarith
  · linarith

end Zeta23Ext.Bridge.FourPoint
