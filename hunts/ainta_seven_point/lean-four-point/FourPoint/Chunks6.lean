import FourPoint.Cells

/-! Chunk module 6 of 16 of the three-dimensional table.  Each lemma is one
subtree of at most 110 leaves of one box's bisection tree; `FourPoint/Boxes.lean` routes
the box down to them.  Cutting the tree this way gives each subtree its own
heartbeat budget and lets `lake` compile them in parallel. -/

noncomputable section
namespace Zeta23Ext.Bridge.FourPoint

set_option maxHeartbeats 20000000 in
lemma ch_12 (x y z : ℝ) (hx1 : (131/128:ℝ) ≤ x) (hx2 : x ≤ (529/512:ℝ))
    (hy1 : (63/32:ℝ) ≤ y) (hy2 : y ≤ (509/256:ℝ))
    (hz1 : (131/128:ℝ) ≤ z) (hz2 : z ≤ (267/256:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total y (1013/512:ℝ) with hc | hc
  · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
    have hw1 : (4884069333/10000000000000:ℝ) ≤ wfun y := wc_132 y (by linarith) (by linarith)
    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_13 z (by linarith) (by linarith)
    have hw3 : (28217469/5000000000000:ℝ) ≤ wfun (x + y) := by
      rcases le_total (x + y) (3:ℝ) with hq30 | hq30
      · exact le_trans (by norm_num) (wc_321 (x + y) (by linarith) (by linarith))
      exact le_trans (by norm_num) (wc_327 (x + y) (by linarith) (by linarith))
    have hw5 : (31471/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_702 (x + y + z) (by linarith) (by linarith)
    linarith
  · rcases le_total z (529/512:ℝ) with hc | hc
    · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
      have hw1 : (3192232409/10000000000000:ℝ) ≤ wfun y := wc_165 y (by linarith) (by linarith)
      have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
      have hw5 : (10750333/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_759 (x + y + z) (by linarith) (by linarith)
      linarith
    · rcases le_total x (1053/1024:ℝ) with hc | hc
      · have hw0 : (3436255003/5000000000000:ℝ) ≤ wfun x := wc_11 x (by linarith) (by linarith)
        have hw1 : (3192232409/10000000000000:ℝ) ≤ wfun y := wc_165 y (by linarith) (by linarith)
        have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_19 z (by linarith) (by linarith)
        have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_330 (x + y) (by linarith) (by linarith)
        have hw5 : (165310021/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_782 (x + y + z) (by linarith) (by linarith)
        linarith
      · rcases le_total y (2031/1024:ℝ) with hc | hc
        · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_15 x (by linarith) (by linarith)
          have hw1 : (200253263/500000000000:ℝ) ≤ wfun y := wc_164 y (by linarith) (by linarith)
          have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_19 z (by linarith) (by linarith)
          have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_335 (x + y) (by linarith) (by linarith)
          have hw5 : (128356097/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_795 (x + y + z) (by linarith) (by linarith)
          linarith
        · rcases le_total z (1063/1024:ℝ) with hc | hc
          · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_15 x (by linarith) (by linarith)
            have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_196 y (by linarith) (by linarith)
            have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
            have hw5 : (184146301/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_802 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_15 x (by linarith) (by linarith)
            have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_196 y (by linarith) (by linarith)
            have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
            have hw4 : (293481/2500000000000:ℝ) ≤ wfun (y + z) := wc_363 (y + z) (by linarith) (by linarith)
            have hw5 : (99536523/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_813 (x + y + z) (by linarith) (by linarith)
            linarith

set_option maxHeartbeats 20000000 in
lemma ch_15 (x y z : ℝ) (hx1 : (529/512:ℝ) ≤ x) (hx2 : x ≤ (267/256:ℝ))
    (hy1 : (1013/512:ℝ) ≤ y) (hy2 : y ≤ (509/256:ℝ))
    (hz1 : (529/512:ℝ) ≤ z) (hz2 : z ≤ (267/256:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (1063/1024:ℝ) with hc | hc
  · rcases le_total y (2031/1024:ℝ) with hc | hc
    · rcases le_total z (1063/1024:ℝ) with hc | hc
      · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
        have hw1 : (200253263/500000000000:ℝ) ≤ wfun y := wc_164 y (by linarith) (by linarith)
        have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
        have hw5 : (184146301/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_802 (x + y + z) (by linarith) (by linarith)
        linarith
      · rcases le_total x (2121/2048:ℝ) with hc | hc
        · have hw0 : (1888462017/5000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
          have hw1 : (200253263/500000000000:ℝ) ≤ wfun y := wc_164 y (by linarith) (by linarith)
          have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
          have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_340 (x + y) (by linarith) (by linarith)
          have hw5 : (498883881/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_812 (x + y + z) (by linarith) (by linarith)
          linarith
        · rcases le_total y (4057/2048:ℝ) with hc | hc
          · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
            have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_163 y (by linarith) (by linarith)
            have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
            have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_345 (x + y) (by linarith) (by linarith)
            have hw5 : (572192259/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_817 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total z (2131/2048:ℝ) with hc | hc
            · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
              have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_180 y (by linarith) (by linarith)
              have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
              have hw5 : (162636919/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_820 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
              have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_180 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
              have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_361 (y + z) (by linarith) (by linarith)
              have hw5 : (183045519/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_839 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total z (1063/1024:ℝ) with hc | hc
      · rcases le_total x (2121/2048:ℝ) with hc | hc
        · have hw0 : (1888462017/5000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
          have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_196 y (by linarith) (by linarith)
          have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
          have hw5 : (498883881/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_812 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
          have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_196 y (by linarith) (by linarith)
          have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
          have hw5 : (570814473/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_818 (x + y + z) (by linarith) (by linarith)
          linarith
      · rcases le_total x (2121/2048:ℝ) with hc | hc
        · rcases le_total y (4067/2048:ℝ) with hc | hc
          · have hw0 : (1888462017/5000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
            have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_195 y (by linarith) (by linarith)
            have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
            have hw4 : (235547/2000000000000:ℝ) ≤ wfun (y + z) := wc_362 (y + z) (by linarith) (by linarith)
            have hw5 : (648981217/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_821 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1888462017/5000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
            have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_210 y (by linarith) (by linarith)
            have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
            have hw4 : (5174037/5000000000000:ℝ) ≤ wfun (y + z) := wc_390 (y + z) (by linarith) (by linarith)
            have hw5 : (730420113/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_840 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (4067/2048:ℝ) with hc | hc
          · rcases le_total z (2131/2048:ℝ) with hc | hc
            · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
              have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_195 y (by linarith) (by linarith)
              have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
              have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_361 (y + z) (by linarith) (by linarith)
              have hw5 : (183045519/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_839 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
              have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_195 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
              have hw4 : (2076333/2000000000000:ℝ) ≤ wfun (y + z) := wc_389 (y + z) (by linarith) (by linarith)
              have hw5 : (12788137/156250000000:ℝ) ≤ wfun (x + y + z) := wc_847 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (2131/2048:ℝ) with hc | hc
            · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
              have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_210 y (by linarith) (by linarith)
              have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
              have hw3 : (1181561/10000000000000:ℝ) ≤ wfun (x + y) := wc_361 (x + y) (by linarith) (by linarith)
              have hw4 : (2076333/2000000000000:ℝ) ≤ wfun (y + z) := wc_389 (y + z) (by linarith) (by linarith)
              have hw5 : (12788137/156250000000:ℝ) ≤ wfun (x + y + z) := wc_847 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (4247/4096:ℝ) with hc | hc
              · have hw0 : (1676998161/5000000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
                have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_210 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                have hw3 : (29587/250000000000:ℝ) ≤ wfun (x + y) := wc_360 (x + y) (by linarith) (by linarith)
                have hw4 : (14329561/5000000000000:ℝ) ≤ wfun (y + z) := wc_419 (y + z) (by linarith) (by linarith)
                have hw5 : (910381357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_859 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_22 x (by linarith) (by linarith)
                have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_210 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                have hw3 : (465149/1000000000000:ℝ) ≤ wfun (x + y) := wc_375 (x + y) (by linarith) (by linarith)
                have hw4 : (14329561/5000000000000:ℝ) ≤ wfun (y + z) := wc_419 (y + z) (by linarith) (by linarith)
                have hw5 : (191513687/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_867 (x + y + z) (by linarith) (by linarith)
                linarith
  · rcases le_total y (2031/1024:ℝ) with hc | hc
    · rcases le_total z (1063/1024:ℝ) with hc | hc
      · rcases le_total x (2131/2048:ℝ) with hc | hc
        · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
          have hw1 : (200253263/500000000000:ℝ) ≤ wfun y := wc_164 y (by linarith) (by linarith)
          have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
          have hw5 : (498883881/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_812 (x + y + z) (by linarith) (by linarith)
          linarith
        · rcases le_total y (4057/2048:ℝ) with hc | hc
          · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_31 x (by linarith) (by linarith)
            have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_163 y (by linarith) (by linarith)
            have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
            have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_340 (y + z) (by linarith) (by linarith)
            have hw5 : (572192259/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_817 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total z (2121/2048:ℝ) with hc | hc
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_31 x (by linarith) (by linarith)
              have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_180 y (by linarith) (by linarith)
              have hw2 : (1888462017/5000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
              have hw3 : (1181561/10000000000000:ℝ) ≤ wfun (x + y) := wc_361 (x + y) (by linarith) (by linarith)
              have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_345 (y + z) (by linarith) (by linarith)
              have hw5 : (162636919/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_820 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_31 x (by linarith) (by linarith)
              have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_180 y (by linarith) (by linarith)
              have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
              have hw3 : (1181561/10000000000000:ℝ) ≤ wfun (x + y) := wc_361 (x + y) (by linarith) (by linarith)
              have hw5 : (183045519/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_839 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (2131/2048:ℝ) with hc | hc
        · rcases le_total y (4057/2048:ℝ) with hc | hc
          · rcases le_total z (2131/2048:ℝ) with hc | hc
            · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
              have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_163 y (by linarith) (by linarith)
              have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
              have hw5 : (162636919/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_820 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (4257/4096:ℝ) with hc | hc
              · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_163 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                have hw5 : (14661301/200000000000:ℝ) ≤ wfun (x + y + z) := wc_838 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
                have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_163 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                have hw5 : (193917431/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_843 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (2131/2048:ℝ) with hc | hc
            · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
              have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_180 y (by linarith) (by linarith)
              have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
              have hw5 : (183045519/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_839 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (4257/4096:ℝ) with hc | hc
              · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_180 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_361 (y + z) (by linarith) (by linarith)
                have hw5 : (81942717/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_846 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total y (8119/4096:ℝ) with hc | hc
                · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
                  have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_179 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                  have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_353 (x + y) (by linarith) (by linarith)
                  have hw4 : (29587/250000000000:ℝ) ≤ wfun (y + z) := wc_360 (y + z) (by linarith) (by linarith)
                  have hw5 : (865374359/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_855 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
                  have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                  have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_359 (x + y) (by linarith) (by linarith)
                  have hw4 : (465149/1000000000000:ℝ) ≤ wfun (y + z) := wc_375 (y + z) (by linarith) (by linarith)
                  have hw5 : (227869559/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_858 (x + y + z) (by linarith) (by linarith)
                  linarith
        · rcases le_total y (4057/2048:ℝ) with hc | hc
          · rcases le_total z (2131/2048:ℝ) with hc | hc
            · rcases le_total x (4267/4096:ℝ) with hc | hc
              · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_163 y (by linarith) (by linarith)
                have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                have hw5 : (14661301/200000000000:ℝ) ≤ wfun (x + y + z) := wc_838 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_163 y (by linarith) (by linarith)
                have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                have hw3 : (41/1250000000000:ℝ) ≤ wfun (x + y) := wc_354 (x + y) (by linarith) (by linarith)
                have hw5 : (193917431/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_843 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (4267/4096:ℝ) with hc | hc
              · rcases le_total y (8109/4096:ℝ) with hc | hc
                · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                  have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_162 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                  have hw5 : (820415059/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_845 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                  have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_172 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                  have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_353 (x + y) (by linarith) (by linarith)
                  have hw4 : (41/1250000000000:ℝ) ≤ wfun (y + z) := wc_354 (y + z) (by linarith) (by linarith)
                  have hw5 : (865374359/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_855 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (8109/4096:ℝ) with hc | hc
                · rcases le_total z (4267/4096:ℝ) with hc | hc
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                    have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_162 y (by linarith) (by linarith)
                    have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                    have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_353 (x + y) (by linarith) (by linarith)
                    have hw5 : (866417641/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_854 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                    have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_162 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                    have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_353 (x + y) (by linarith) (by linarith)
                    have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_353 (y + z) (by linarith) (by linarith)
                    have hw5 : (3564753/39062500000:ℝ) ≤ wfun (x + y + z) := wc_857 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total z (4267/4096:ℝ) with hc | hc
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                    have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_172 y (by linarith) (by linarith)
                    have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                    have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_359 (x + y) (by linarith) (by linarith)
                    have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_353 (y + z) (by linarith) (by linarith)
                    have hw5 : (3564753/39062500000:ℝ) ≤ wfun (x + y + z) := wc_857 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                    have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_172 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                    have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_359 (x + y) (by linarith) (by linarith)
                    have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_359 (y + z) (by linarith) (by linarith)
                    have hw5 : (959876941/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_865 (x + y + z) (by linarith) (by linarith)
                    linarith
          · rcases le_total z (2131/2048:ℝ) with hc | hc
            · rcases le_total x (4267/4096:ℝ) with hc | hc
              · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_180 y (by linarith) (by linarith)
                have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                have hw3 : (29587/250000000000:ℝ) ≤ wfun (x + y) := wc_360 (x + y) (by linarith) (by linarith)
                have hw5 : (81942717/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_846 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total y (8119/4096:ℝ) with hc | hc
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                  have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_179 y (by linarith) (by linarith)
                  have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                  have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_374 (x + y) (by linarith) (by linarith)
                  have hw5 : (865374359/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_855 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                  have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
                  have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                  have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_387 (x + y) (by linarith) (by linarith)
                  have hw4 : (41/1250000000000:ℝ) ≤ wfun (y + z) := wc_354 (y + z) (by linarith) (by linarith)
                  have hw5 : (227869559/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_858 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total x (4267/4096:ℝ) with hc | hc
              · rcases le_total y (8119/4096:ℝ) with hc | hc
                · rcases le_total z (4267/4096:ℝ) with hc | hc
                  · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                    have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_179 y (by linarith) (by linarith)
                    have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                    have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_359 (x + y) (by linarith) (by linarith)
                    have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_359 (y + z) (by linarith) (by linarith)
                    have hw5 : (3564753/39062500000:ℝ) ≤ wfun (x + y + z) := wc_857 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                    have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_179 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                    have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_359 (x + y) (by linarith) (by linarith)
                    have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_374 (y + z) (by linarith) (by linarith)
                    have hw5 : (959876941/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_865 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total z (4267/4096:ℝ) with hc | hc
                  · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                    have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
                    have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                    have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_374 (x + y) (by linarith) (by linarith)
                    have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_374 (y + z) (by linarith) (by linarith)
                    have hw5 : (959876941/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_865 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                    have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                    have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_374 (x + y) (by linarith) (by linarith)
                    have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_387 (y + z) (by linarith) (by linarith)
                    have hw5 : (126039153/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_871 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total y (8119/4096:ℝ) with hc | hc
                · rcases le_total z (4267/4096:ℝ) with hc | hc
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                    have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_179 y (by linarith) (by linarith)
                    have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                    have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_374 (x + y) (by linarith) (by linarith)
                    have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_359 (y + z) (by linarith) (by linarith)
                    have hw5 : (959876941/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_865 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · rcases le_total x (8539/8192:ℝ) with hc | hc
                    · have hw0 : (1770787537/10000000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
                      have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_179 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                      have hw3 : (4662827/10000000000000:ℝ) ≤ wfun (x + y) := wc_373 (x + y) (by linarith) (by linarith)
                      have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_374 (y + z) (by linarith) (by linarith)
                      have hw5 : (1008920431/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_870 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                      have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_179 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                      have hw3 : (7258139/10000000000000:ℝ) ≤ wfun (x + y) := wc_380 (x + y) (by linarith) (by linarith)
                      have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_374 (y + z) (by linarith) (by linarith)
                      have hw5 : (5167889/50000000000:ℝ) ≤ wfun (x + y + z) := wc_884 (x + y + z) (by linarith) (by linarith)
                      linarith
                · rcases le_total z (4267/4096:ℝ) with hc | hc
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                    have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
                    have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                    have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_387 (x + y) (by linarith) (by linarith)
                    have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_374 (y + z) (by linarith) (by linarith)
                    have hw5 : (126039153/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_871 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · rcases le_total x (8539/8192:ℝ) with hc | hc
                    · have hw0 : (1770787537/10000000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
                      have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                      have hw3 : (5211923/5000000000000:ℝ) ≤ wfun (x + y) := wc_386 (x + y) (by linarith) (by linarith)
                      have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_387 (y + z) (by linarith) (by linarith)
                      have hw5 : (264629371/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_886 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                      have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                      have hw3 : (3539799/2500000000000:ℝ) ≤ wfun (x + y) := wc_396 (x + y) (by linarith) (by linarith)
                      have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_387 (y + z) (by linarith) (by linarith)
                      have hw5 : (33866839/312500000000:ℝ) ≤ wfun (x + y + z) := wc_892 (x + y + z) (by linarith) (by linarith)
                      linarith
    · rcases le_total z (1063/1024:ℝ) with hc | hc
      · rcases le_total x (2131/2048:ℝ) with hc | hc
        · rcases le_total y (4067/2048:ℝ) with hc | hc
          · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
            have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_195 y (by linarith) (by linarith)
            have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
            have hw3 : (1181561/10000000000000:ℝ) ≤ wfun (x + y) := wc_361 (x + y) (by linarith) (by linarith)
            have hw5 : (648981217/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_821 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
            have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_210 y (by linarith) (by linarith)
            have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
            have hw3 : (2076333/2000000000000:ℝ) ≤ wfun (x + y) := wc_389 (x + y) (by linarith) (by linarith)
            have hw5 : (730420113/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_840 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (4067/2048:ℝ) with hc | hc
          · rcases le_total z (2121/2048:ℝ) with hc | hc
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_31 x (by linarith) (by linarith)
              have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_195 y (by linarith) (by linarith)
              have hw2 : (1888462017/5000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
              have hw3 : (2076333/2000000000000:ℝ) ≤ wfun (x + y) := wc_389 (x + y) (by linarith) (by linarith)
              have hw5 : (183045519/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_839 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_31 x (by linarith) (by linarith)
              have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_195 y (by linarith) (by linarith)
              have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
              have hw3 : (2076333/2000000000000:ℝ) ≤ wfun (x + y) := wc_389 (x + y) (by linarith) (by linarith)
              have hw5 : (12788137/156250000000:ℝ) ≤ wfun (x + y + z) := wc_847 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (2121/2048:ℝ) with hc | hc
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_31 x (by linarith) (by linarith)
              have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_210 y (by linarith) (by linarith)
              have hw2 : (1888462017/5000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
              have hw3 : (14329561/5000000000000:ℝ) ≤ wfun (x + y) := wc_419 (x + y) (by linarith) (by linarith)
              have hw5 : (12788137/156250000000:ℝ) ≤ wfun (x + y + z) := wc_847 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (4267/4096:ℝ) with hc | hc
              · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_210 y (by linarith) (by linarith)
                have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
                have hw3 : (2870559/1000000000000:ℝ) ≤ wfun (x + y) := wc_418 (x + y) (by linarith) (by linarith)
                have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_361 (y + z) (by linarith) (by linarith)
                have hw5 : (910381357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_859 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_210 y (by linarith) (by linarith)
                have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
                have hw3 : (20626673/5000000000000:ℝ) ≤ wfun (x + y) := wc_436 (x + y) (by linarith) (by linarith)
                have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_361 (y + z) (by linarith) (by linarith)
                have hw5 : (191513687/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_867 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total x (2131/2048:ℝ) with hc | hc
        · rcases le_total y (4067/2048:ℝ) with hc | hc
          · rcases le_total z (2131/2048:ℝ) with hc | hc
            · rcases le_total x (4257/4096:ℝ) with hc | hc
              · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_195 y (by linarith) (by linarith)
                have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                have hw3 : (29587/250000000000:ℝ) ≤ wfun (x + y) := wc_360 (x + y) (by linarith) (by linarith)
                have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_361 (y + z) (by linarith) (by linarith)
                have hw5 : (81942717/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_846 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
                have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_195 y (by linarith) (by linarith)
                have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                have hw3 : (465149/1000000000000:ℝ) ≤ wfun (x + y) := wc_375 (x + y) (by linarith) (by linarith)
                have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_361 (y + z) (by linarith) (by linarith)
                have hw5 : (864332647/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_856 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (4257/4096:ℝ) with hc | hc
              · rcases le_total y (8129/4096:ℝ) with hc | hc
                · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                  have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                  have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_359 (x + y) (by linarith) (by linarith)
                  have hw4 : (649907/625000000000:ℝ) ≤ wfun (y + z) := wc_388 (y + z) (by linarith) (by linarith)
                  have hw5 : (227869559/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_858 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                  have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                  have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_374 (x + y) (by linarith) (by linarith)
                  have hw4 : (736743/400000000000:ℝ) ≤ wfun (y + z) := wc_404 (y + z) (by linarith) (by linarith)
                  have hw5 : (958721819/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_866 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (8129/4096:ℝ) with hc | hc
                · rcases le_total z (4267/4096:ℝ) with hc | hc
                  · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
                    have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
                    have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                    have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_374 (x + y) (by linarith) (by linarith)
                    have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_387 (y + z) (by linarith) (by linarith)
                    have hw5 : (959876941/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_865 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
                    have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                    have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_374 (x + y) (by linarith) (by linarith)
                    have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_403 (y + z) (by linarith) (by linarith)
                    have hw5 : (126039153/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_871 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total z (4267/4096:ℝ) with hc | hc
                  · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
                    have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
                    have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                    have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_387 (x + y) (by linarith) (by linarith)
                    have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_403 (y + z) (by linarith) (by linarith)
                    have hw5 : (126039153/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_871 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
                    have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                    have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_387 (x + y) (by linarith) (by linarith)
                    have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_417 (y + z) (by linarith) (by linarith)
                    have hw5 : (1057880619/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_887 (x + y + z) (by linarith) (by linarith)
                    linarith
          · rcases le_total z (2131/2048:ℝ) with hc | hc
            · rcases le_total x (4257/4096:ℝ) with hc | hc
              · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_210 y (by linarith) (by linarith)
                have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                have hw3 : (649907/625000000000:ℝ) ≤ wfun (x + y) := wc_388 (x + y) (by linarith) (by linarith)
                have hw4 : (2076333/2000000000000:ℝ) ≤ wfun (y + z) := wc_389 (y + z) (by linarith) (by linarith)
                have hw5 : (910381357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_859 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
                have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_210 y (by linarith) (by linarith)
                have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                have hw3 : (736743/400000000000:ℝ) ≤ wfun (x + y) := wc_404 (x + y) (by linarith) (by linarith)
                have hw4 : (2076333/2000000000000:ℝ) ≤ wfun (y + z) := wc_389 (y + z) (by linarith) (by linarith)
                have hw5 : (191513687/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_867 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (4257/4096:ℝ) with hc | hc
              · rcases le_total y (8139/4096:ℝ) with hc | hc
                · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                  have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                  have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_387 (x + y) (by linarith) (by linarith)
                  have hw4 : (2870559/1000000000000:ℝ) ≤ wfun (y + z) := wc_418 (y + z) (by linarith) (by linarith)
                  have hw5 : (1007100179/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_872 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                  have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                  have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_403 (x + y) (by linarith) (by linarith)
                  have hw4 : (20626673/5000000000000:ℝ) ≤ wfun (y + z) := wc_436 (y + z) (by linarith) (by linarith)
                  have hw5 : (528304163/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_888 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (8139/4096:ℝ) with hc | hc
                · rcases le_total z (4267/4096:ℝ) with hc | hc
                  · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
                    have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
                    have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                    have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_403 (x + y) (by linarith) (by linarith)
                    have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_417 (y + z) (by linarith) (by linarith)
                    have hw5 : (1057880619/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_887 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
                    have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                    have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_403 (x + y) (by linarith) (by linarith)
                    have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_435 (y + z) (by linarith) (by linarith)
                    have hw5 : (1108574073/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_896 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total z (4267/4096:ℝ) with hc | hc
                  · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
                    have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
                    have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                    have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_417 (x + y) (by linarith) (by linarith)
                    have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_435 (y + z) (by linarith) (by linarith)
                    have hw5 : (1108574073/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_896 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
                    have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                    have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_417 (x + y) (by linarith) (by linarith)
                    have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_449 (y + z) (by linarith) (by linarith)
                    have hw5 : (290097117/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_909 (x + y + z) (by linarith) (by linarith)
                    linarith
        · rcases le_total y (4067/2048:ℝ) with hc | hc
          · rcases le_total z (2131/2048:ℝ) with hc | hc
            · rcases le_total x (4267/4096:ℝ) with hc | hc
              · rcases le_total y (8129/4096:ℝ) with hc | hc
                · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                  have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
                  have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                  have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_387 (x + y) (by linarith) (by linarith)
                  have hw4 : (29587/250000000000:ℝ) ≤ wfun (y + z) := wc_360 (y + z) (by linarith) (by linarith)
                  have hw5 : (227869559/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_858 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                  have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
                  have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                  have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_403 (x + y) (by linarith) (by linarith)
                  have hw4 : (465149/1000000000000:ℝ) ≤ wfun (y + z) := wc_375 (y + z) (by linarith) (by linarith)
                  have hw5 : (958721819/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_866 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (8129/4096:ℝ) with hc | hc
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                  have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
                  have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                  have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_403 (x + y) (by linarith) (by linarith)
                  have hw4 : (29587/250000000000:ℝ) ≤ wfun (y + z) := wc_360 (y + z) (by linarith) (by linarith)
                  have hw5 : (958721819/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_866 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total z (4257/4096:ℝ) with hc | hc
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                    have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
                    have hw2 : (2586175977/10000000000000:ℝ) ≤ wfun z := wc_23 z (by linarith) (by linarith)
                    have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_417 (x + y) (by linarith) (by linarith)
                    have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_374 (y + z) (by linarith) (by linarith)
                    have hw5 : (126039153/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_871 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                    have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
                    have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
                    have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_417 (x + y) (by linarith) (by linarith)
                    have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_387 (y + z) (by linarith) (by linarith)
                    have hw5 : (1057880619/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_887 (x + y + z) (by linarith) (by linarith)
                    linarith
            · rcases le_total x (4267/4096:ℝ) with hc | hc
              · rcases le_total y (8129/4096:ℝ) with hc | hc
                · rcases le_total z (4267/4096:ℝ) with hc | hc
                  · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                    have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
                    have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                    have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_387 (x + y) (by linarith) (by linarith)
                    have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_387 (y + z) (by linarith) (by linarith)
                    have hw5 : (126039153/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_871 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                    have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                    have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_387 (x + y) (by linarith) (by linarith)
                    have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_403 (y + z) (by linarith) (by linarith)
                    have hw5 : (1057880619/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_887 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total z (4267/4096:ℝ) with hc | hc
                  · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                    have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
                    have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                    have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_403 (x + y) (by linarith) (by linarith)
                    have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_403 (y + z) (by linarith) (by linarith)
                    have hw5 : (1057880619/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_887 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · rcases le_total x (8529/8192:ℝ) with hc | hc
                    · have hw0 : (1038927507/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                      have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                      have hw3 : (1846343/1000000000000:ℝ) ≤ wfun (x + y) := wc_402 (x + y) (by linarith) (by linarith)
                      have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_417 (y + z) (by linarith) (by linarith)
                      have hw5 : (554620627/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_895 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_32 x (by linarith) (by linarith)
                      have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                      have hw3 : (23335779/10000000000000:ℝ) ≤ wfun (x + y) := wc_410 (x + y) (by linarith) (by linarith)
                      have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_417 (y + z) (by linarith) (by linarith)
                      have hw5 : (1135024061/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_904 (x + y + z) (by linarith) (by linarith)
                      linarith
              · rcases le_total y (8129/4096:ℝ) with hc | hc
                · rcases le_total z (4267/4096:ℝ) with hc | hc
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                    have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
                    have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                    have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_403 (x + y) (by linarith) (by linarith)
                    have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_387 (y + z) (by linarith) (by linarith)
                    have hw5 : (1057880619/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_887 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · rcases le_total x (8539/8192:ℝ) with hc | hc
                    · have hw0 : (1770787537/10000000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
                      have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                      have hw3 : (1846343/1000000000000:ℝ) ≤ wfun (x + y) := wc_402 (x + y) (by linarith) (by linarith)
                      have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_403 (y + z) (by linarith) (by linarith)
                      have hw5 : (554620627/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_895 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · rcases le_total y (16253/8192:ℝ) with hc | hc
                      · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                        have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                        have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                        have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_409 (x + y) (by linarith) (by linarith)
                        have hw4 : (1846343/1000000000000:ℝ) ≤ wfun (y + z) := wc_402 (y + z) (by linarith) (by linarith)
                        have hw5 : (567853581/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_903 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                        have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                        have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                        have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
                        have hw4 : (23335779/10000000000000:ℝ) ≤ wfun (y + z) := wc_410 (y + z) (by linarith) (by linarith)
                        have hw5 : (145223163/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_907 (x + y + z) (by linarith) (by linarith)
                        linarith
                · rcases le_total z (4267/4096:ℝ) with hc | hc
                  · rcases le_total x (8539/8192:ℝ) with hc | hc
                    · have hw0 : (1770787537/10000000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
                      have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
                      have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                      have hw3 : (28775469/10000000000000:ℝ) ≤ wfun (x + y) := wc_416 (x + y) (by linarith) (by linarith)
                      have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_403 (y + z) (by linarith) (by linarith)
                      have hw5 : (554620627/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_895 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                      have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
                      have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                      have hw3 : (6956343/2000000000000:ℝ) ≤ wfun (x + y) := wc_428 (x + y) (by linarith) (by linarith)
                      have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_403 (y + z) (by linarith) (by linarith)
                      have hw5 : (1135024061/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_904 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · rcases le_total x (8539/8192:ℝ) with hc | hc
                    · have hw0 : (1770787537/10000000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
                      have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                      have hw3 : (28775469/10000000000000:ℝ) ≤ wfun (x + y) := wc_416 (x + y) (by linarith) (by linarith)
                      have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_417 (y + z) (by linarith) (by linarith)
                      have hw5 : (36283957/312500000000:ℝ) ≤ wfun (x + y + z) := wc_908 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · rcases le_total y (16263/8192:ℝ) with hc | hc
                      · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                        have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                        have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                        have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_427 (x + y) (by linarith) (by linarith)
                        have hw4 : (28775469/10000000000000:ℝ) ≤ wfun (y + z) := wc_416 (y + z) (by linarith) (by linarith)
                        have hw5 : (594071357/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_915 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                        have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
                        have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                        have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_433 (x + y) (by linarith) (by linarith)
                        have hw4 : (6956343/2000000000000:ℝ) ≤ wfun (y + z) := wc_428 (y + z) (by linarith) (by linarith)
                        have hw5 : (1214778741/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_921 (x + y + z) (by linarith) (by linarith)
                        linarith
          · rcases le_total z (2131/2048:ℝ) with hc | hc
            · rcases le_total x (4267/4096:ℝ) with hc | hc
              · rcases le_total y (8139/4096:ℝ) with hc | hc
                · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                  have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
                  have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                  have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_417 (x + y) (by linarith) (by linarith)
                  have hw4 : (649907/625000000000:ℝ) ≤ wfun (y + z) := wc_388 (y + z) (by linarith) (by linarith)
                  have hw5 : (1007100179/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_872 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                  have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
                  have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                  have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_435 (x + y) (by linarith) (by linarith)
                  have hw4 : (736743/400000000000:ℝ) ≤ wfun (y + z) := wc_404 (y + z) (by linarith) (by linarith)
                  have hw5 : (528304163/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_888 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (8139/4096:ℝ) with hc | hc
                · rcases le_total z (4257/4096:ℝ) with hc | hc
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                    have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
                    have hw2 : (2586175977/10000000000000:ℝ) ≤ wfun z := wc_23 z (by linarith) (by linarith)
                    have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_435 (x + y) (by linarith) (by linarith)
                    have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_387 (y + z) (by linarith) (by linarith)
                    have hw5 : (1057880619/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_887 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                    have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
                    have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
                    have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_435 (x + y) (by linarith) (by linarith)
                    have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_403 (y + z) (by linarith) (by linarith)
                    have hw5 : (1108574073/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_896 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total z (4257/4096:ℝ) with hc | hc
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                    have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
                    have hw2 : (2586175977/10000000000000:ℝ) ≤ wfun z := wc_23 z (by linarith) (by linarith)
                    have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_449 (x + y) (by linarith) (by linarith)
                    have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_403 (y + z) (by linarith) (by linarith)
                    have hw5 : (1108574073/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_896 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                    have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
                    have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
                    have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_449 (x + y) (by linarith) (by linarith)
                    have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_417 (y + z) (by linarith) (by linarith)
                    have hw5 : (290097117/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_909 (x + y + z) (by linarith) (by linarith)
                    linarith
            · rcases le_total x (4267/4096:ℝ) with hc | hc
              · rcases le_total y (8139/4096:ℝ) with hc | hc
                · rcases le_total z (4267/4096:ℝ) with hc | hc
                  · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                    have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
                    have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                    have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_417 (x + y) (by linarith) (by linarith)
                    have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_417 (y + z) (by linarith) (by linarith)
                    have hw5 : (1108574073/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_896 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · rcases le_total x (8529/8192:ℝ) with hc | hc
                    · have hw0 : (1038927507/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                      have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                      have hw3 : (28775469/10000000000000:ℝ) ≤ wfun (x + y) := wc_416 (x + y) (by linarith) (by linarith)
                      have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_435 (y + z) (by linarith) (by linarith)
                      have hw5 : (36283957/312500000000:ℝ) ≤ wfun (x + y + z) := wc_908 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_32 x (by linarith) (by linarith)
                      have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                      have hw3 : (6956343/2000000000000:ℝ) ≤ wfun (x + y) := wc_428 (x + y) (by linarith) (by linarith)
                      have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_435 (y + z) (by linarith) (by linarith)
                      have hw5 : (118742829/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_916 (x + y + z) (by linarith) (by linarith)
                      linarith
                · rcases le_total z (4267/4096:ℝ) with hc | hc
                  · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                    have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
                    have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                    have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_435 (x + y) (by linarith) (by linarith)
                    have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_435 (y + z) (by linarith) (by linarith)
                    have hw5 : (290097117/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_909 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                    have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                    have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_435 (x + y) (by linarith) (by linarith)
                    have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_449 (y + z) (by linarith) (by linarith)
                    have hw5 : (1213318631/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_923 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total y (8139/4096:ℝ) with hc | hc
                · rcases le_total z (4267/4096:ℝ) with hc | hc
                  · rcases le_total x (8539/8192:ℝ) with hc | hc
                    · have hw0 : (1770787537/10000000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
                      have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
                      have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                      have hw3 : (4135373/1000000000000:ℝ) ≤ wfun (x + y) := wc_434 (x + y) (by linarith) (by linarith)
                      have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_417 (y + z) (by linarith) (by linarith)
                      have hw5 : (36283957/312500000000:ℝ) ≤ wfun (x + y + z) := wc_908 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                      have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
                      have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                      have hw3 : (48490713/10000000000000:ℝ) ≤ wfun (x + y) := wc_442 (x + y) (by linarith) (by linarith)
                      have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_417 (y + z) (by linarith) (by linarith)
                      have hw5 : (118742829/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_916 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · rcases le_total x (8539/8192:ℝ) with hc | hc
                    · have hw0 : (1770787537/10000000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
                      have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                      have hw3 : (4135373/1000000000000:ℝ) ≤ wfun (x + y) := wc_434 (x + y) (by linarith) (by linarith)
                      have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_435 (y + z) (by linarith) (by linarith)
                      have hw5 : (303512103/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_922 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · rcases le_total y (16273/8192:ℝ) with hc | hc
                      · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                        have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                        have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                        have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_441 (x + y) (by linarith) (by linarith)
                        have hw4 : (4135373/1000000000000:ℝ) ≤ wfun (y + z) := wc_434 (y + z) (by linarith) (by linarith)
                        have hw5 : (155211591/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_937 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                        have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                        have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                        have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
                        have hw4 : (48490713/10000000000000:ℝ) ≤ wfun (y + z) := wc_442 (y + z) (by linarith) (by linarith)
                        have hw5 : (634442007/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_944 (x + y + z) (by linarith) (by linarith)
                        linarith
                · rcases le_total z (4267/4096:ℝ) with hc | hc
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                    have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
                    have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                    have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_449 (x + y) (by linarith) (by linarith)
                    have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_435 (y + z) (by linarith) (by linarith)
                    have hw5 : (1213318631/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_923 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · rcases le_total x (8539/8192:ℝ) with hc | hc
                    · have hw0 : (1770787537/10000000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
                      have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                      have hw3 : (2809593/500000000000:ℝ) ≤ wfun (x + y) := wc_448 (x + y) (by linarith) (by linarith)
                      have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_449 (y + z) (by linarith) (by linarith)
                      have hw5 : (634060693/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_945 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                      have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                      have hw3 : (64456359/10000000000000:ℝ) ≤ wfun (x + y) := wc_458 (x + y) (by linarith) (by linarith)
                      have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_449 (y + z) (by linarith) (by linarith)
                      have hw5 : (647786457/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_955 (x + y + z) (by linarith) (by linarith)
                      linarith

set_option maxHeartbeats 20000000 in
lemma ch_39 (x y z : ℝ) (hx1 : (267/256:ℝ) ≤ x) (hx2 : x ≤ (539/512:ℝ))
    (hy1 : (63/32:ℝ) ≤ y) (hy2 : y ≤ (1013/512:ℝ))
    (hz1 : (131/128:ℝ) ≤ z) (hz2 : z ≤ (529/512:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (1073/1024:ℝ) with hc | hc
  · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
    have hw1 : (4884069333/10000000000000:ℝ) ≤ wfun y := wc_132 y (by linarith) (by linarith)
    have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
    have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := by
      rcases le_total (y + z) (3:ℝ) with hq40 | hq40
      · exact le_trans (by norm_num) (wc_321 (y + z) (by linarith) (by linarith))
      exact le_trans (by norm_num) (wc_327 (y + z) (by linarith) (by linarith))
    have hw5 : (165310021/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_782 (x + y + z) (by linarith) (by linarith)
    linarith
  · rcases le_total y (2021/1024:ℝ) with hc | hc
    · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
      have hw1 : (2946158453/5000000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
      have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
      have hw4 : (70009749/5000000000000:ℝ) ≤ wfun (y + z) := by
        rcases le_total (y + z) (3:ℝ) with hq40 | hq40
        · exact le_trans (by norm_num) (wc_321 (y + z) (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_325 (y + z) (by linarith) (by linarith))
      have hw5 : (128356097/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_795 (x + y + z) (by linarith) (by linarith)
      linarith
    · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
      have hw1 : (4902043129/10000000000000:ℝ) ≤ wfun y := wc_144 y (by linarith) (by linarith)
      have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
      have hw3 : (293481/2500000000000:ℝ) ≤ wfun (x + y) := wc_363 (x + y) (by linarith) (by linarith)
      have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := by
        rcases le_total (y + z) (3:ℝ) with hq40 | hq40
        · exact le_trans (by norm_num) (wc_323 (y + z) (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_327 (y + z) (by linarith) (by linarith))
      have hw5 : (183260287/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_803 (x + y + z) (by linarith) (by linarith)
      linarith

set_option maxHeartbeats 20000000 in
lemma ch_47 (x y z : ℝ) (hx1 : (267/256:ℝ) ≤ x) (hx2 : x ≤ (2141/2048:ℝ))
    (hy1 : (2031/1024:ℝ) ≤ y) (hy2 : y ≤ (509/256:ℝ))
    (hz1 : (1063/1024:ℝ) ≤ z) (hz2 : z ≤ (267/256:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total y (4067/2048:ℝ) with hc | hc
  · rcases le_total z (2131/2048:ℝ) with hc | hc
    · rcases le_total x (4277/4096:ℝ) with hc | hc
      · rcases le_total y (8129/4096:ℝ) with hc | hc
        · rcases le_total z (4257/4096:ℝ) with hc | hc
          · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
            have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
            have hw2 : (2586175977/10000000000000:ℝ) ≤ wfun z := wc_23 z (by linarith) (by linarith)
            have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_417 (x + y) (by linarith) (by linarith)
            have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_359 (y + z) (by linarith) (by linarith)
            have hw5 : (126039153/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_871 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
            have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
            have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
            have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_417 (x + y) (by linarith) (by linarith)
            have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_374 (y + z) (by linarith) (by linarith)
            have hw5 : (1057880619/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_887 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (4257/4096:ℝ) with hc | hc
          · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
            have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
            have hw2 : (2586175977/10000000000000:ℝ) ≤ wfun z := wc_23 z (by linarith) (by linarith)
            have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_435 (x + y) (by linarith) (by linarith)
            have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_374 (y + z) (by linarith) (by linarith)
            have hw5 : (1057880619/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_887 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
            have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
            have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
            have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_435 (x + y) (by linarith) (by linarith)
            have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_387 (y + z) (by linarith) (by linarith)
            have hw5 : (1108574073/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_896 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total y (8129/4096:ℝ) with hc | hc
        · rcases le_total z (4257/4096:ℝ) with hc | hc
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
            have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
            have hw2 : (2586175977/10000000000000:ℝ) ≤ wfun z := wc_23 z (by linarith) (by linarith)
            have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_435 (x + y) (by linarith) (by linarith)
            have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_359 (y + z) (by linarith) (by linarith)
            have hw5 : (1057880619/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_887 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
            have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
            have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
            have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_435 (x + y) (by linarith) (by linarith)
            have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_374 (y + z) (by linarith) (by linarith)
            have hw5 : (1108574073/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_896 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (4257/4096:ℝ) with hc | hc
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
            have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
            have hw2 : (2586175977/10000000000000:ℝ) ≤ wfun z := wc_23 z (by linarith) (by linarith)
            have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_449 (x + y) (by linarith) (by linarith)
            have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_374 (y + z) (by linarith) (by linarith)
            have hw5 : (1108574073/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_896 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (8559/8192:ℝ) with hc | hc
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
              have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
              have hw3 : (2809593/500000000000:ℝ) ≤ wfun (x + y) := wc_448 (x + y) (by linarith) (by linarith)
              have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_387 (y + z) (by linarith) (by linarith)
              have hw5 : (36283957/312500000000:ℝ) ≤ wfun (x + y + z) := wc_908 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
              have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
              have hw3 : (64456359/10000000000000:ℝ) ≤ wfun (x + y) := wc_458 (x + y) (by linarith) (by linarith)
              have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_387 (y + z) (by linarith) (by linarith)
              have hw5 : (118742829/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_916 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total x (4277/4096:ℝ) with hc | hc
      · rcases le_total y (8129/4096:ℝ) with hc | hc
        · rcases le_total z (4267/4096:ℝ) with hc | hc
          · rcases le_total x (8549/8192:ℝ) with hc | hc
            · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
              have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
              have hw3 : (28775469/10000000000000:ℝ) ≤ wfun (x + y) := wc_416 (x + y) (by linarith) (by linarith)
              have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_387 (y + z) (by linarith) (by linarith)
              have hw5 : (554620627/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_895 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
              have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
              have hw3 : (6956343/2000000000000:ℝ) ≤ wfun (x + y) := wc_428 (x + y) (by linarith) (by linarith)
              have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_387 (y + z) (by linarith) (by linarith)
              have hw5 : (1135024061/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_904 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (8549/8192:ℝ) with hc | hc
            · rcases le_total y (16253/8192:ℝ) with hc | hc
              · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
                have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
                have hw4 : (1846343/1000000000000:ℝ) ≤ wfun (y + z) := wc_402 (y + z) (by linarith) (by linarith)
                have hw5 : (145223163/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_907 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
                have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_427 (x + y) (by linarith) (by linarith)
                have hw4 : (23335779/10000000000000:ℝ) ≤ wfun (y + z) := wc_410 (y + z) (by linarith) (by linarith)
                have hw5 : (594071357/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_915 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16253/8192:ℝ) with hc | hc
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_427 (x + y) (by linarith) (by linarith)
                have hw4 : (1846343/1000000000000:ℝ) ≤ wfun (y + z) := wc_402 (y + z) (by linarith) (by linarith)
                have hw5 : (594071357/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_915 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total z (8539/8192:ℝ) with hc | hc
                · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                  have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                  have hw2 : (1770787537/10000000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                  have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_433 (x + y) (by linarith) (by linarith)
                  have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
                  have hw5 : (1215509621/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_920 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                  have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_35 z (by linarith) (by linarith)
                  have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_433 (x + y) (by linarith) (by linarith)
                  have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
                  have hw5 : (155304961/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_936 (x + y + z) (by linarith) (by linarith)
                  linarith
        · rcases le_total z (4267/4096:ℝ) with hc | hc
          · rcases le_total x (8549/8192:ℝ) with hc | hc
            · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
              have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
              have hw3 : (4135373/1000000000000:ℝ) ≤ wfun (x + y) := wc_434 (x + y) (by linarith) (by linarith)
              have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_403 (y + z) (by linarith) (by linarith)
              have hw5 : (36283957/312500000000:ℝ) ≤ wfun (x + y + z) := wc_908 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
              have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
              have hw3 : (48490713/10000000000000:ℝ) ≤ wfun (x + y) := wc_442 (x + y) (by linarith) (by linarith)
              have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_403 (y + z) (by linarith) (by linarith)
              have hw5 : (118742829/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_916 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (8549/8192:ℝ) with hc | hc
            · rcases le_total y (16263/8192:ℝ) with hc | hc
              · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
                have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_433 (x + y) (by linarith) (by linarith)
                have hw4 : (28775469/10000000000000:ℝ) ≤ wfun (y + z) := wc_416 (y + z) (by linarith) (by linarith)
                have hw5 : (1214778741/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_921 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
                have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_441 (x + y) (by linarith) (by linarith)
                have hw4 : (6956343/2000000000000:ℝ) ≤ wfun (y + z) := wc_428 (y + z) (by linarith) (by linarith)
                have hw5 : (155211591/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_937 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16263/8192:ℝ) with hc | hc
              · rcases le_total z (8539/8192:ℝ) with hc | hc
                · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                  have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                  have hw2 : (1770787537/10000000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                  have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_441 (x + y) (by linarith) (by linarith)
                  have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
                  have hw5 : (155304961/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_936 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                  have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_35 z (by linarith) (by linarith)
                  have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_441 (x + y) (by linarith) (by linarith)
                  have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
                  have hw5 : (253929443/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_943 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
                have hw4 : (6956343/2000000000000:ℝ) ≤ wfun (y + z) := wc_428 (y + z) (by linarith) (by linarith)
                have hw5 : (634442007/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_944 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total y (8129/4096:ℝ) with hc | hc
        · rcases le_total z (4267/4096:ℝ) with hc | hc
          · rcases le_total x (8559/8192:ℝ) with hc | hc
            · rcases le_total y (16253/8192:ℝ) with hc | hc
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_433 (x + y) (by linarith) (by linarith)
                have hw4 : (5211923/5000000000000:ℝ) ≤ wfun (y + z) := wc_386 (y + z) (by linarith) (by linarith)
                have hw5 : (145223163/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_907 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_441 (x + y) (by linarith) (by linarith)
                have hw4 : (3539799/2500000000000:ℝ) ≤ wfun (y + z) := wc_396 (y + z) (by linarith) (by linarith)
                have hw5 : (594071357/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_915 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16253/8192:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_441 (x + y) (by linarith) (by linarith)
                have hw4 : (5211923/5000000000000:ℝ) ≤ wfun (y + z) := wc_386 (y + z) (by linarith) (by linarith)
                have hw5 : (594071357/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_915 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
                have hw4 : (3539799/2500000000000:ℝ) ≤ wfun (y + z) := wc_396 (y + z) (by linarith) (by linarith)
                have hw5 : (1214778741/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_921 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (8559/8192:ℝ) with hc | hc
            · rcases le_total y (16253/8192:ℝ) with hc | hc
              · rcases le_total z (8539/8192:ℝ) with hc | hc
                · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                  have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                  have hw2 : (1770787537/10000000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                  have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_433 (x + y) (by linarith) (by linarith)
                  have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
                  have hw5 : (1215509621/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_920 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                  have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_35 z (by linarith) (by linarith)
                  have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_433 (x + y) (by linarith) (by linarith)
                  have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
                  have hw5 : (155304961/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_936 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (8539/8192:ℝ) with hc | hc
                · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                  have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                  have hw2 : (1770787537/10000000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                  have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_441 (x + y) (by linarith) (by linarith)
                  have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
                  have hw5 : (155304961/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_936 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                  have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_35 z (by linarith) (by linarith)
                  have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_441 (x + y) (by linarith) (by linarith)
                  have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
                  have hw5 : (253929443/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_943 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total y (16253/8192:ℝ) with hc | hc
              · rcases le_total z (8539/8192:ℝ) with hc | hc
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                  have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                  have hw2 : (1770787537/10000000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                  have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_441 (x + y) (by linarith) (by linarith)
                  have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
                  have hw5 : (155304961/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_936 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                  have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_35 z (by linarith) (by linarith)
                  have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_441 (x + y) (by linarith) (by linarith)
                  have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
                  have hw5 : (253929443/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_943 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (8539/8192:ℝ) with hc | hc
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                  have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                  have hw2 : (1770787537/10000000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                  have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
                  have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
                  have hw5 : (253929443/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_943 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                  have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_35 z (by linarith) (by linarith)
                  have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
                  have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
                  have hw5 : (1297131539/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_953 (x + y + z) (by linarith) (by linarith)
                  linarith
        · rcases le_total z (4267/4096:ℝ) with hc | hc
          · rcases le_total x (8559/8192:ℝ) with hc | hc
            · rcases le_total y (16263/8192:ℝ) with hc | hc
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
                have hw4 : (1846343/1000000000000:ℝ) ≤ wfun (y + z) := wc_402 (y + z) (by linarith) (by linarith)
                have hw5 : (1214778741/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_921 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
                have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
                have hw4 : (23335779/10000000000000:ℝ) ≤ wfun (y + z) := wc_410 (y + z) (by linarith) (by linarith)
                have hw5 : (155211591/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_937 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16263/8192:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
                have hw4 : (1846343/1000000000000:ℝ) ≤ wfun (y + z) := wc_402 (y + z) (by linarith) (by linarith)
                have hw5 : (155211591/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_937 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
                have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
                have hw4 : (23335779/10000000000000:ℝ) ≤ wfun (y + z) := wc_410 (y + z) (by linarith) (by linarith)
                have hw5 : (634442007/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_944 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (8559/8192:ℝ) with hc | hc
            · rcases le_total y (16263/8192:ℝ) with hc | hc
              · rcases le_total z (8539/8192:ℝ) with hc | hc
                · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                  have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                  have hw2 : (1770787537/10000000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                  have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
                  have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
                  have hw5 : (253929443/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_943 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                  have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_35 z (by linarith) (by linarith)
                  have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
                  have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
                  have hw5 : (1297131539/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_953 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (8539/8192:ℝ) with hc | hc
                · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                  have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
                  have hw2 : (1770787537/10000000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                  have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
                  have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
                  have hw5 : (1297131539/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_953 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                  have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_35 z (by linarith) (by linarith)
                  have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
                  have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
                  have hw5 : (1324891991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_963 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total y (16263/8192:ℝ) with hc | hc
              · rcases le_total z (8539/8192:ℝ) with hc | hc
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                  have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                  have hw2 : (1770787537/10000000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                  have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
                  have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
                  have hw5 : (1297131539/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_953 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                  have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_35 z (by linarith) (by linarith)
                  have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
                  have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
                  have hw5 : (1324891991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_963 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (8539/8192:ℝ) with hc | hc
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                  have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
                  have hw2 : (1770787537/10000000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                  have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
                  have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
                  have hw5 : (1324891991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_963 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                  have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_35 z (by linarith) (by linarith)
                  have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
                  have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
                  have hw5 : (1352927899/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_978 (x + y + z) (by linarith) (by linarith)
                  linarith
  · rcases le_total z (2131/2048:ℝ) with hc | hc
    · rcases le_total x (4277/4096:ℝ) with hc | hc
      · rcases le_total y (8139/4096:ℝ) with hc | hc
        · rcases le_total z (4257/4096:ℝ) with hc | hc
          · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
            have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
            have hw2 : (2586175977/10000000000000:ℝ) ≤ wfun z := wc_23 z (by linarith) (by linarith)
            have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_449 (x + y) (by linarith) (by linarith)
            have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_387 (y + z) (by linarith) (by linarith)
            have hw5 : (1108574073/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_896 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
            have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
            have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
            have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_449 (x + y) (by linarith) (by linarith)
            have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_403 (y + z) (by linarith) (by linarith)
            have hw5 : (290097117/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_909 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (4257/4096:ℝ) with hc | hc
          · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
            have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
            have hw2 : (2586175977/10000000000000:ℝ) ≤ wfun z := wc_23 z (by linarith) (by linarith)
            have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_465 (x + y) (by linarith) (by linarith)
            have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_403 (y + z) (by linarith) (by linarith)
            have hw5 : (290097117/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_909 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
            have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
            have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
            have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_465 (x + y) (by linarith) (by linarith)
            have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_417 (y + z) (by linarith) (by linarith)
            have hw5 : (1213318631/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_923 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total y (8139/4096:ℝ) with hc | hc
        · rcases le_total z (4257/4096:ℝ) with hc | hc
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
            have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
            have hw2 : (2586175977/10000000000000:ℝ) ≤ wfun z := wc_23 z (by linarith) (by linarith)
            have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_465 (x + y) (by linarith) (by linarith)
            have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_387 (y + z) (by linarith) (by linarith)
            have hw5 : (290097117/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_909 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (8559/8192:ℝ) with hc | hc
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
              have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
              have hw3 : (73283389/10000000000000:ℝ) ≤ wfun (x + y) := wc_464 (x + y) (by linarith) (by linarith)
              have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_403 (y + z) (by linarith) (by linarith)
              have hw5 : (303512103/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_922 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
              have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
              have hw3 : (82672123/10000000000000:ℝ) ≤ wfun (x + y) := wc_472 (x + y) (by linarith) (by linarith)
              have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_403 (y + z) (by linarith) (by linarith)
              have hw5 : (124094633/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_938 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (4257/4096:ℝ) with hc | hc
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
            have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
            have hw2 : (2586175977/10000000000000:ℝ) ≤ wfun z := wc_23 z (by linarith) (by linarith)
            have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_479 (x + y) (by linarith) (by linarith)
            have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_403 (y + z) (by linarith) (by linarith)
            have hw5 : (1213318631/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_923 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
            have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
            have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
            have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_479 (x + y) (by linarith) (by linarith)
            have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_417 (y + z) (by linarith) (by linarith)
            have hw5 : (1267359331/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_946 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total x (4277/4096:ℝ) with hc | hc
      · rcases le_total y (8139/4096:ℝ) with hc | hc
        · rcases le_total z (4267/4096:ℝ) with hc | hc
          · rcases le_total x (8549/8192:ℝ) with hc | hc
            · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
              have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
              have hw3 : (2809593/500000000000:ℝ) ≤ wfun (x + y) := wc_448 (x + y) (by linarith) (by linarith)
              have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_417 (y + z) (by linarith) (by linarith)
              have hw5 : (303512103/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_922 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
              have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
              have hw3 : (64456359/10000000000000:ℝ) ≤ wfun (x + y) := wc_458 (x + y) (by linarith) (by linarith)
              have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_417 (y + z) (by linarith) (by linarith)
              have hw5 : (124094633/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_938 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (8549/8192:ℝ) with hc | hc
            · rcases le_total y (16273/8192:ℝ) with hc | hc
              · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
                have hw4 : (4135373/1000000000000:ℝ) ≤ wfun (y + z) := wc_434 (y + z) (by linarith) (by linarith)
                have hw5 : (634442007/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_944 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
                have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
                have hw4 : (48490713/10000000000000:ℝ) ≤ wfun (y + z) := wc_442 (y + z) (by linarith) (by linarith)
                have hw5 : (648175967/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_954 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16273/8192:ℝ) with hc | hc
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
                have hw4 : (4135373/1000000000000:ℝ) ≤ wfun (y + z) := wc_434 (y + z) (by linarith) (by linarith)
                have hw5 : (648175967/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_954 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
                have hw4 : (48490713/10000000000000:ℝ) ≤ wfun (y + z) := wc_442 (y + z) (by linarith) (by linarith)
                have hw5 : (1324095821/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_964 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (4267/4096:ℝ) with hc | hc
          · rcases le_total x (8549/8192:ℝ) with hc | hc
            · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
              have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
              have hw3 : (73283389/10000000000000:ℝ) ≤ wfun (x + y) := wc_464 (x + y) (by linarith) (by linarith)
              have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_435 (y + z) (by linarith) (by linarith)
              have hw5 : (634060693/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_945 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
              have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
              have hw3 : (82672123/10000000000000:ℝ) ≤ wfun (x + y) := wc_472 (x + y) (by linarith) (by linarith)
              have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_435 (y + z) (by linarith) (by linarith)
              have hw5 : (647786457/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_955 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (8549/8192:ℝ) with hc | hc
            · rcases le_total y (16283/8192:ℝ) with hc | hc
              · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
                have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
                have hw4 : (2809593/500000000000:ℝ) ≤ wfun (y + z) := wc_448 (y + z) (by linarith) (by linarith)
                have hw5 : (1324095821/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_964 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
                have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
                have hw4 : (64456359/10000000000000:ℝ) ≤ wfun (y + z) := wc_458 (y + z) (by linarith) (by linarith)
                have hw5 : (338028751/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_979 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16283/8192:ℝ) with hc | hc
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
                have hw4 : (2809593/500000000000:ℝ) ≤ wfun (y + z) := wc_448 (y + z) (by linarith) (by linarith)
                have hw5 : (338028751/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_979 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
                have hw4 : (64456359/10000000000000:ℝ) ≤ wfun (y + z) := wc_458 (y + z) (by linarith) (by linarith)
                have hw5 : (690204403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_988 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total y (8139/4096:ℝ) with hc | hc
        · rcases le_total z (4267/4096:ℝ) with hc | hc
          · rcases le_total x (8559/8192:ℝ) with hc | hc
            · rcases le_total y (16273/8192:ℝ) with hc | hc
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
                have hw4 : (28775469/10000000000000:ℝ) ≤ wfun (y + z) := wc_416 (y + z) (by linarith) (by linarith)
                have hw5 : (634442007/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_944 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
                have hw4 : (6956343/2000000000000:ℝ) ≤ wfun (y + z) := wc_428 (y + z) (by linarith) (by linarith)
                have hw5 : (648175967/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_954 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16273/8192:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
                have hw4 : (28775469/10000000000000:ℝ) ≤ wfun (y + z) := wc_416 (y + z) (by linarith) (by linarith)
                have hw5 : (648175967/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_954 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
                have hw4 : (6956343/2000000000000:ℝ) ≤ wfun (y + z) := wc_428 (y + z) (by linarith) (by linarith)
                have hw5 : (1324095821/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_964 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (8559/8192:ℝ) with hc | hc
            · rcases le_total y (16273/8192:ℝ) with hc | hc
              · rcases le_total z (8539/8192:ℝ) with hc | hc
                · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                  have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                  have hw2 : (1770787537/10000000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                  have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
                  have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
                  have hw5 : (1324891991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_963 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                  have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_35 z (by linarith) (by linarith)
                  have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
                  have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
                  have hw5 : (1352927899/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_978 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (8539/8192:ℝ) with hc | hc
                · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                  have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                  have hw2 : (1770787537/10000000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                  have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
                  have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
                  have hw5 : (1352927899/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_978 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                  have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_35 z (by linarith) (by linarith)
                  have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
                  have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
                  have hw5 : (690619293/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_987 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total y (16273/8192:ℝ) with hc | hc
              · rcases le_total z (8539/8192:ℝ) with hc | hc
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                  have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                  have hw2 : (1770787537/10000000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                  have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
                  have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
                  have hw5 : (1352927899/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_978 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                  have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_35 z (by linarith) (by linarith)
                  have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
                  have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
                  have hw5 : (690619293/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_987 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (8539/8192:ℝ) with hc | hc
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                  have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                  have hw2 : (1770787537/10000000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                  have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
                  have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
                  have hw5 : (690619293/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_987 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                  have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_35 z (by linarith) (by linarith)
                  have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
                  have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
                  have hw5 : (1409823377/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_999 (x + y + z) (by linarith) (by linarith)
                  linarith
        · rcases le_total z (4267/4096:ℝ) with hc | hc
          · rcases le_total x (8559/8192:ℝ) with hc | hc
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
              have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
              have hw3 : (46310863/5000000000000:ℝ) ≤ wfun (x + y) := wc_478 (x + y) (by linarith) (by linarith)
              have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_435 (y + z) (by linarith) (by linarith)
              have hw5 : (1323300249/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_965 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total y (16283/8192:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
                have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
                have hw4 : (4135373/1000000000000:ℝ) ≤ wfun (y + z) := wc_434 (y + z) (by linarith) (by linarith)
                have hw5 : (338028751/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_979 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
                have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
                have hw4 : (48490713/10000000000000:ℝ) ≤ wfun (y + z) := wc_442 (y + z) (by linarith) (by linarith)
                have hw5 : (690204403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_988 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (8559/8192:ℝ) with hc | hc
            · rcases le_total y (16283/8192:ℝ) with hc | hc
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
                have hw4 : (2809593/500000000000:ℝ) ≤ wfun (y + z) := wc_448 (y + z) (by linarith) (by linarith)
                have hw5 : (690204403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_988 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
                have hw4 : (64456359/10000000000000:ℝ) ≤ wfun (y + z) := wc_458 (y + z) (by linarith) (by linarith)
                have hw5 : (176122069/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1000 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16283/8192:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
                have hw4 : (2809593/500000000000:ℝ) ≤ wfun (y + z) := wc_448 (y + z) (by linarith) (by linarith)
                have hw5 : (176122069/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1000 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
                have hw4 : (64456359/10000000000000:ℝ) ≤ wfun (y + z) := wc_458 (y + z) (by linarith) (by linarith)
                have hw5 : (718908779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1009 (x + y + z) (by linarith) (by linarith)
                linarith

set_option maxHeartbeats 20000000 in
lemma ch_73 (x y z : ℝ) (hx1 : (4297/4096:ℝ) ≤ x) (hx2 : x ≤ (2151/2048:ℝ))
    (hy1 : (4047/2048:ℝ) ≤ y) (hy2 : y ≤ (1013/512:ℝ))
    (hz1 : (2141/2048:ℝ) ≤ z) (hz2 : z ≤ (1073/1024:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total y (8099/4096:ℝ) with hc | hc
  · rcases le_total z (4287/4096:ℝ) with hc | hc
    · rcases le_total x (8599/8192:ℝ) with hc | hc
      · rcases le_total y (16193/8192:ℝ) with hc | hc
        · rcases le_total z (8569/8192:ℝ) with hc | hc
          · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
            have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
            have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
            have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
            have hw4 : (1187329/10000000000000:ℝ) ≤ wfun (y + z) := wc_357 (y + z) (by linarith) (by linarith)
            have hw5 : (253929443/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_943 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
            have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
            have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
            have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
            have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
            have hw5 : (1297131539/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_953 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (8569/8192:ℝ) with hc | hc
          · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
            have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
            have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
            have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_409 (x + y) (by linarith) (by linarith)
            have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
            have hw5 : (1297131539/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_953 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (17193/16384:ℝ) with hc | hc
            · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (2920523/1250000000000:ℝ) ≤ wfun (x + y) := wc_408 (x + y) (by linarith) (by linarith)
              have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
              have hw5 : (1325290301/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_962 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_80 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (26016381/10000000000000:ℝ) ≤ wfun (x + y) := wc_412 (x + y) (by linarith) (by linarith)
              have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
              have hw5 : (669639019/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_974 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total y (16193/8192:ℝ) with hc | hc
        · rcases le_total z (8569/8192:ℝ) with hc | hc
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
            have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
            have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_409 (x + y) (by linarith) (by linarith)
            have hw4 : (1187329/10000000000000:ℝ) ≤ wfun (y + z) := wc_357 (y + z) (by linarith) (by linarith)
            have hw5 : (1297131539/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_953 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
            have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
            have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_409 (x + y) (by linarith) (by linarith)
            have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
            have hw5 : (1324891991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_963 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (8569/8192:ℝ) with hc | hc
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
            have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
            have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
            have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
            have hw5 : (1324891991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_963 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
            have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
            have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
            have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
            have hw5 : (1352927899/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_978 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total x (8599/8192:ℝ) with hc | hc
      · rcases le_total y (16193/8192:ℝ) with hc | hc
        · rcases le_total z (8579/8192:ℝ) with hc | hc
          · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
            have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
            have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
            have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
            have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
            have hw5 : (1324891991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_963 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
            have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
            have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
            have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
            have hw5 : (1352927899/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_978 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (8579/8192:ℝ) with hc | hc
          · rcases le_total x (17193/16384:ℝ) with hc | hc
            · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (2920523/1250000000000:ℝ) ≤ wfun (x + y) := wc_408 (x + y) (by linarith) (by linarith)
              have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
              have hw5 : (84583411/625000000000:ℝ) ≤ wfun (x + y + z) := wc_977 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_80 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (26016381/10000000000000:ℝ) ≤ wfun (x + y) := wc_412 (x + y) (by linarith) (by linarith)
              have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
              have hw5 : (1367459827/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_983 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17193/16384:ℝ) with hc | hc
            · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (2920523/1250000000000:ℝ) ≤ wfun (x + y) := wc_408 (x + y) (by linarith) (by linarith)
              have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
              have hw5 : (1381653711/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_986 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_80 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (26016381/10000000000000:ℝ) ≤ wfun (x + y) := wc_412 (x + y) (by linarith) (by linarith)
              have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
              have hw5 : (1395916139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_995 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total y (16193/8192:ℝ) with hc | hc
        · rcases le_total z (8579/8192:ℝ) with hc | hc
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
            have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
            have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_409 (x + y) (by linarith) (by linarith)
            have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
            have hw5 : (1352927899/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_978 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
            have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_409 (x + y) (by linarith) (by linarith)
            have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
            have hw5 : (690619293/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_987 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (8579/8192:ℝ) with hc | hc
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
            have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
            have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
            have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
            have hw5 : (690619293/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_987 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
            have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
            have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
            have hw5 : (1409823377/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_999 (x + y + z) (by linarith) (by linarith)
            linarith
  · rcases le_total z (4287/4096:ℝ) with hc | hc
    · rcases le_total x (8599/8192:ℝ) with hc | hc
      · rcases le_total y (16203/8192:ℝ) with hc | hc
        · rcases le_total z (8569/8192:ℝ) with hc | hc
          · rcases le_total x (17193/16384:ℝ) with hc | hc
            · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (3601311/1250000000000:ℝ) ≤ wfun (x + y) := wc_414 (x + y) (by linarith) (by linarith)
              have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
              have hw5 : (1325290301/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_962 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_80 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (6349281/2000000000000:ℝ) ≤ wfun (x + y) := wc_424 (x + y) (by linarith) (by linarith)
              have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
              have hw5 : (669639019/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_974 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17193/16384:ℝ) with hc | hc
            · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (3601311/1250000000000:ℝ) ≤ wfun (x + y) := wc_414 (x + y) (by linarith) (by linarith)
              have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
              have hw5 : (84583411/625000000000:ℝ) ≤ wfun (x + y + z) := wc_977 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_80 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (6349281/2000000000000:ℝ) ≤ wfun (x + y) := wc_424 (x + y) (by linarith) (by linarith)
              have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
              have hw5 : (1367459827/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_983 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (8569/8192:ℝ) with hc | hc
          · rcases le_total x (17193/16384:ℝ) with hc | hc
            · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (8706009/2500000000000:ℝ) ≤ wfun (x + y) := wc_426 (x + y) (by linarith) (by linarith)
              have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
              have hw5 : (84583411/625000000000:ℝ) ≤ wfun (x + y + z) := wc_977 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_80 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (38043279/10000000000000:ℝ) ≤ wfun (x + y) := wc_430 (x + y) (by linarith) (by linarith)
              have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
              have hw5 : (1367459827/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_983 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17193/16384:ℝ) with hc | hc
            · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (8706009/2500000000000:ℝ) ≤ wfun (x + y) := wc_426 (x + y) (by linarith) (by linarith)
              have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
              have hw5 : (1381653711/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_986 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_80 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (38043279/10000000000000:ℝ) ≤ wfun (x + y) := wc_430 (x + y) (by linarith) (by linarith)
              have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
              have hw5 : (1395916139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_995 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total y (16203/8192:ℝ) with hc | hc
        · rcases le_total z (8569/8192:ℝ) with hc | hc
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
            have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
            have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_427 (x + y) (by linarith) (by linarith)
            have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
            have hw5 : (1352927899/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_978 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
            have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
            have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_427 (x + y) (by linarith) (by linarith)
            have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
            have hw5 : (690619293/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_987 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (8569/8192:ℝ) with hc | hc
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
            have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
            have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_433 (x + y) (by linarith) (by linarith)
            have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
            have hw5 : (690619293/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_987 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (17203/16384:ℝ) with hc | hc
            · have hw0 : (207931583/5000000000000:ℝ) ≤ wfun x := wc_81 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (10351009/2500000000000:ℝ) ≤ wfun (x + y) := wc_432 (x + y) (by linarith) (by linarith)
              have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
              have hw5 : (1410247029/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_998 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_83 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (22453103/5000000000000:ℝ) ≤ wfun (x + y) := wc_438 (x + y) (by linarith) (by linarith)
              have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
              have hw5 : (356161573/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1004 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total x (8599/8192:ℝ) with hc | hc
      · rcases le_total y (16203/8192:ℝ) with hc | hc
        · rcases le_total z (8579/8192:ℝ) with hc | hc
          · rcases le_total x (17193/16384:ℝ) with hc | hc
            · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (3601311/1250000000000:ℝ) ≤ wfun (x + y) := wc_414 (x + y) (by linarith) (by linarith)
              have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
              have hw5 : (1381653711/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_986 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_80 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (6349281/2000000000000:ℝ) ≤ wfun (x + y) := wc_424 (x + y) (by linarith) (by linarith)
              have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
              have hw5 : (1395916139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_995 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17193/16384:ℝ) with hc | hc
            · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (3601311/1250000000000:ℝ) ≤ wfun (x + y) := wc_414 (x + y) (by linarith) (by linarith)
              have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
              have hw5 : (1410247029/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_998 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_80 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (6349281/2000000000000:ℝ) ≤ wfun (x + y) := wc_424 (x + y) (by linarith) (by linarith)
              have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
              have hw5 : (356161573/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1004 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (8579/8192:ℝ) with hc | hc
          · rcases le_total x (17193/16384:ℝ) with hc | hc
            · rcases le_total y (32411/16384:ℝ) with hc | hc
              · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
                have hw1 : (4977151133/10000000000000:ℝ) ≤ wfun y := wc_157 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
                have hw4 : (7088219/5000000000000:ℝ) ≤ wfun (y + z) := wc_394 (y + z) (by linarith) (by linarith)
                have hw5 : (1410670839/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_997 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
                have hw1 : (61471063/125000000000:ℝ) ≤ wfun y := wc_159 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
                have hw4 : (650401/400000000000:ℝ) ≤ wfun (y + z) := wc_398 (y + z) (by linarith) (by linarith)
                have hw5 : (712537199/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1003 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_80 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (38043279/10000000000000:ℝ) ≤ wfun (x + y) := wc_430 (x + y) (by linarith) (by linarith)
              have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
              have hw5 : (356161573/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1004 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17193/16384:ℝ) with hc | hc
            · rcases le_total y (32411/16384:ℝ) with hc | hc
              · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
                have hw1 : (4977151133/10000000000000:ℝ) ≤ wfun y := wc_157 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
                have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
                have hw5 : (719773133/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1006 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
                have hw1 : (61471063/125000000000:ℝ) ≤ wfun y := wc_159 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
                have hw4 : (10426997/5000000000000:ℝ) ≤ wfun (y + z) := wc_406 (y + z) (by linarith) (by linarith)
                have hw5 : (1454086357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1027 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_80 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (38043279/10000000000000:ℝ) ≤ wfun (x + y) := wc_430 (x + y) (by linarith) (by linarith)
              have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
              have hw5 : (726824801/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1028 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total y (16203/8192:ℝ) with hc | hc
        · rcases le_total z (8579/8192:ℝ) with hc | hc
          · rcases le_total x (17203/16384:ℝ) with hc | hc
            · have hw0 : (207931583/5000000000000:ℝ) ≤ wfun x := wc_81 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (8706009/2500000000000:ℝ) ≤ wfun (x + y) := wc_426 (x + y) (by linarith) (by linarith)
              have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
              have hw5 : (1410247029/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_998 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_83 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (38043279/10000000000000:ℝ) ≤ wfun (x + y) := wc_430 (x + y) (by linarith) (by linarith)
              have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
              have hw5 : (356161573/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1004 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
            have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_427 (x + y) (by linarith) (by linarith)
            have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
            have hw5 : (1438681587/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1008 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (8579/8192:ℝ) with hc | hc
          · rcases le_total x (17203/16384:ℝ) with hc | hc
            · have hw0 : (207931583/5000000000000:ℝ) ≤ wfun x := wc_81 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (10351009/2500000000000:ℝ) ≤ wfun (x + y) := wc_432 (x + y) (by linarith) (by linarith)
              have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
              have hw5 : (287822769/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1007 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_83 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (22453103/5000000000000:ℝ) ≤ wfun (x + y) := wc_438 (x + y) (by linarith) (by linarith)
              have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
              have hw5 : (726824801/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1028 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17203/16384:ℝ) with hc | hc
            · have hw0 : (207931583/5000000000000:ℝ) ≤ wfun x := wc_81 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (10351009/2500000000000:ℝ) ≤ wfun (x + y) := wc_432 (x + y) (by linarith) (by linarith)
              have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
              have hw5 : (58730139/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1031 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_83 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (22453103/5000000000000:ℝ) ≤ wfun (x + y) := wc_438 (x + y) (by linarith) (by linarith)
              have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
              have hw5 : (1482925379/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1037 (x + y + z) (by linarith) (by linarith)
              linarith

set_option maxHeartbeats 20000000 in
lemma ch_90 (x y z : ℝ) (hx1 : (2141/2048:ℝ) ≤ x) (hx2 : x ≤ (4287/4096:ℝ))
    (hy1 : (1013/512:ℝ) ≤ y) (hy2 : y ≤ (8109/4096:ℝ))
    (hz1 : (2141/2048:ℝ) ≤ z) (hz2 : z ≤ (1073/1024:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total z (4287/4096:ℝ) with hc | hc
  · rcases le_total x (8569/8192:ℝ) with hc | hc
    · rcases le_total y (16213/8192:ℝ) with hc | hc
      · rcases le_total z (8569/8192:ℝ) with hc | hc
        · rcases le_total x (17133/16384:ℝ) with hc | hc
          · rcases le_total y (32421/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (5220389/5000000000000:ℝ) ≤ wfun (x + y) := wc_383 (x + y) (by linarith) (by linarith)
              have hw4 : (5218271/5000000000000:ℝ) ≤ wfun (y + z) := wc_384 (y + z) (by linarith) (by linarith)
              have hw5 : (24324821/200000000000:ℝ) ≤ wfun (x + y + z) := wc_918 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (12240211/10000000000000:ℝ) ≤ wfun (x + y) := wc_391 (x + y) (by linarith) (by linarith)
              have hw4 : (2447049/2000000000000:ℝ) ≤ wfun (y + z) := wc_392 (y + z) (by linarith) (by linarith)
              have hw5 : (245935877/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_932 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32421/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (12240211/10000000000000:ℝ) ≤ wfun (x + y) := wc_391 (x + y) (by linarith) (by linarith)
              have hw4 : (5218271/5000000000000:ℝ) ≤ wfun (y + z) := wc_384 (y + z) (by linarith) (by linarith)
              have hw5 : (245935877/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_932 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
              have hw4 : (2447049/2000000000000:ℝ) ≤ wfun (y + z) := wc_392 (y + z) (by linarith) (by linarith)
              have hw5 : (1243187209/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_934 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17133/16384:ℝ) with hc | hc
          · rcases le_total y (32421/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (5220389/5000000000000:ℝ) ≤ wfun (x + y) := wc_383 (x + y) (by linarith) (by linarith)
              have hw4 : (7088219/5000000000000:ℝ) ≤ wfun (y + z) := wc_394 (y + z) (by linarith) (by linarith)
              have hw5 : (1243187209/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_934 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (12240211/10000000000000:ℝ) ≤ wfun (x + y) := wc_391 (x + y) (by linarith) (by linarith)
              have hw4 : (650401/400000000000:ℝ) ≤ wfun (y + z) := wc_398 (y + z) (by linarith) (by linarith)
              have hw5 : (1256764439/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_939 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32421/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (12240211/10000000000000:ℝ) ≤ wfun (x + y) := wc_391 (x + y) (by linarith) (by linarith)
              have hw4 : (7088219/5000000000000:ℝ) ≤ wfun (y + z) := wc_394 (y + z) (by linarith) (by linarith)
              have hw5 : (1256764439/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_939 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
              have hw4 : (650401/400000000000:ℝ) ≤ wfun (y + z) := wc_398 (y + z) (by linarith) (by linarith)
              have hw5 : (1270410991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_941 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (8569/8192:ℝ) with hc | hc
        · rcases le_total x (17133/16384:ℝ) with hc | hc
          · rcases le_total y (32431/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
              have hw4 : (7088219/5000000000000:ℝ) ≤ wfun (y + z) := wc_394 (y + z) (by linarith) (by linarith)
              have hw5 : (1243187209/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_934 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
              have hw4 : (650401/400000000000:ℝ) ≤ wfun (y + z) := wc_398 (y + z) (by linarith) (by linarith)
              have hw5 : (1256764439/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_939 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32431/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
              have hw4 : (7088219/5000000000000:ℝ) ≤ wfun (y + z) := wc_394 (y + z) (by linarith) (by linarith)
              have hw5 : (1256764439/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_939 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
              have hw4 : (650401/400000000000:ℝ) ≤ wfun (y + z) := wc_398 (y + z) (by linarith) (by linarith)
              have hw5 : (1270410991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_941 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17133/16384:ℝ) with hc | hc
          · rcases le_total y (32431/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
              have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
              have hw5 : (1270410991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_941 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
              have hw4 : (10426997/5000000000000:ℝ) ≤ wfun (y + z) := wc_406 (y + z) (by linarith) (by linarith)
              have hw5 : (1284126783/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_949 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32431/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
              have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
              have hw5 : (1284126783/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_949 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
              have hw4 : (10426997/5000000000000:ℝ) ≤ wfun (y + z) := wc_406 (y + z) (by linarith) (by linarith)
              have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total y (16213/8192:ℝ) with hc | hc
      · rcases le_total z (8569/8192:ℝ) with hc | hc
        · rcases le_total x (17143/16384:ℝ) with hc | hc
          · rcases le_total y (32421/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
              have hw4 : (5218271/5000000000000:ℝ) ≤ wfun (y + z) := wc_384 (y + z) (by linarith) (by linarith)
              have hw5 : (1243187209/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_934 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
              have hw4 : (2447049/2000000000000:ℝ) ≤ wfun (y + z) := wc_392 (y + z) (by linarith) (by linarith)
              have hw5 : (1256764439/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_939 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32421/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
              have hw4 : (5218271/5000000000000:ℝ) ≤ wfun (y + z) := wc_384 (y + z) (by linarith) (by linarith)
              have hw5 : (1256764439/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_939 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
              have hw4 : (2447049/2000000000000:ℝ) ≤ wfun (y + z) := wc_392 (y + z) (by linarith) (by linarith)
              have hw5 : (1270410991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_941 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17143/16384:ℝ) with hc | hc
          · rcases le_total y (32421/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
              have hw4 : (7088219/5000000000000:ℝ) ≤ wfun (y + z) := wc_394 (y + z) (by linarith) (by linarith)
              have hw5 : (1270410991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_941 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
              have hw4 : (650401/400000000000:ℝ) ≤ wfun (y + z) := wc_398 (y + z) (by linarith) (by linarith)
              have hw5 : (1284126783/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_949 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32421/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
              have hw4 : (7088219/5000000000000:ℝ) ≤ wfun (y + z) := wc_394 (y + z) (by linarith) (by linarith)
              have hw5 : (1284126783/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_949 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
              have hw4 : (650401/400000000000:ℝ) ≤ wfun (y + z) := wc_398 (y + z) (by linarith) (by linarith)
              have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (8569/8192:ℝ) with hc | hc
        · rcases le_total x (17143/16384:ℝ) with hc | hc
          · rcases le_total y (32431/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
              have hw4 : (7088219/5000000000000:ℝ) ≤ wfun (y + z) := wc_394 (y + z) (by linarith) (by linarith)
              have hw5 : (1270410991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_941 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
              have hw4 : (650401/400000000000:ℝ) ≤ wfun (y + z) := wc_398 (y + z) (by linarith) (by linarith)
              have hw5 : (1284126783/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_949 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32431/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
              have hw4 : (7088219/5000000000000:ℝ) ≤ wfun (y + z) := wc_394 (y + z) (by linarith) (by linarith)
              have hw5 : (1284126783/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_949 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
              have hw4 : (650401/400000000000:ℝ) ≤ wfun (y + z) := wc_398 (y + z) (by linarith) (by linarith)
              have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17143/16384:ℝ) with hc | hc
          · rcases le_total y (32431/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
              have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
              have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (17143/16384:ℝ) with hc | hc
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
                have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
                have hw4 : (4172491/2000000000000:ℝ) ≤ wfun (y + z) := wc_405 (y + z) (by linarith) (by linarith)
                have hw5 : (328040051/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_957 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
                have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
                have hw4 : (11686831/5000000000000:ℝ) ≤ wfun (y + z) := wc_407 (y + z) (by linarith) (by linarith)
                have hw5 : (1326087369/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_960 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (32431/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
              have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
              have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (17143/16384:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
                have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
                have hw4 : (4172491/2000000000000:ℝ) ≤ wfun (y + z) := wc_405 (y + z) (by linarith) (by linarith)
                have hw5 : (1326087369/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_960 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
                have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
                have hw4 : (11686831/5000000000000:ℝ) ≤ wfun (y + z) := wc_407 (y + z) (by linarith) (by linarith)
                have hw5 : (1340083459/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_972 (x + y + z) (by linarith) (by linarith)
                linarith
  · rcases le_total x (8569/8192:ℝ) with hc | hc
    · rcases le_total y (16213/8192:ℝ) with hc | hc
      · rcases le_total z (8579/8192:ℝ) with hc | hc
        · rcases le_total x (17133/16384:ℝ) with hc | hc
          · rcases le_total y (32421/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (5220389/5000000000000:ℝ) ≤ wfun (x + y) := wc_383 (x + y) (by linarith) (by linarith)
              have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
              have hw5 : (1270410991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_941 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (12240211/10000000000000:ℝ) ≤ wfun (x + y) := wc_391 (x + y) (by linarith) (by linarith)
              have hw4 : (10426997/5000000000000:ℝ) ≤ wfun (y + z) := wc_406 (y + z) (by linarith) (by linarith)
              have hw5 : (1284126783/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_949 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32421/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (12240211/10000000000000:ℝ) ≤ wfun (x + y) := wc_391 (x + y) (by linarith) (by linarith)
              have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
              have hw5 : (1284126783/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_949 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
              have hw4 : (10426997/5000000000000:ℝ) ≤ wfun (y + z) := wc_406 (y + z) (by linarith) (by linarith)
              have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17133/16384:ℝ) with hc | hc
          · rcases le_total y (32421/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (5220389/5000000000000:ℝ) ≤ wfun (x + y) := wc_383 (x + y) (by linarith) (by linarith)
              have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
              have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (12240211/10000000000000:ℝ) ≤ wfun (x + y) := wc_391 (x + y) (by linarith) (by linarith)
              have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
              have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32421/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (12240211/10000000000000:ℝ) ≤ wfun (x + y) := wc_391 (x + y) (by linarith) (by linarith)
              have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
              have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
              have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
              have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (8579/8192:ℝ) with hc | hc
        · rcases le_total x (17133/16384:ℝ) with hc | hc
          · rcases le_total y (32431/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
              have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
              have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
              have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
              have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32431/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
              have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
              have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
              have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
              have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17133/16384:ℝ) with hc | hc
          · rcases le_total y (32431/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
              have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
              have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
              have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
              have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32431/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
              have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
              have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
              have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
              have hw5 : (676870703/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_976 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total y (16213/8192:ℝ) with hc | hc
      · rcases le_total z (8579/8192:ℝ) with hc | hc
        · rcases le_total x (17143/16384:ℝ) with hc | hc
          · rcases le_total y (32421/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
              have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
              have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
              have hw4 : (10426997/5000000000000:ℝ) ≤ wfun (y + z) := wc_406 (y + z) (by linarith) (by linarith)
              have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32421/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
              have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
              have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
              have hw4 : (10426997/5000000000000:ℝ) ≤ wfun (y + z) := wc_406 (y + z) (by linarith) (by linarith)
              have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17143/16384:ℝ) with hc | hc
          · rcases le_total y (32421/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
              have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
              have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
              have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
              have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32421/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
              have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
              have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
              have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
              have hw5 : (676870703/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_976 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (8579/8192:ℝ) with hc | hc
        · rcases le_total x (17143/16384:ℝ) with hc | hc
          · rcases le_total y (32431/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
              have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
              have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (17153/16384:ℝ) with hc | hc
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
                have hw4 : (13013467/5000000000000:ℝ) ≤ wfun (y + z) := wc_411 (y + z) (by linarith) (by linarith)
                have hw5 : (1340083459/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_972 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
                have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
                have hw4 : (28822173/10000000000000:ℝ) ≤ wfun (y + z) := wc_413 (y + z) (by linarith) (by linarith)
                have hw5 : (338537097/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_975 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (32431/16384:ℝ) with hc | hc
            · rcases le_total z (17153/16384:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
                have hw4 : (11686831/5000000000000:ℝ) ≤ wfun (y + z) := wc_407 (y + z) (by linarith) (by linarith)
                have hw5 : (1340083459/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_972 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
                have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
                have hw4 : (13013467/5000000000000:ℝ) ≤ wfun (y + z) := wc_411 (y + z) (by linarith) (by linarith)
                have hw5 : (338537097/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_975 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (17153/16384:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
                have hw4 : (13013467/5000000000000:ℝ) ≤ wfun (y + z) := wc_411 (y + z) (by linarith) (by linarith)
                have hw5 : (338537097/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_975 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
                have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
                have hw4 : (28822173/10000000000000:ℝ) ≤ wfun (y + z) := wc_413 (y + z) (by linarith) (by linarith)
                have hw5 : (171035259/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_981 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (17143/16384:ℝ) with hc | hc
          · rcases le_total y (32431/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
              have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
              have hw5 : (676870703/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_976 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (17163/16384:ℝ) with hc | hc
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
                have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
                have hw4 : (396991/125000000000:ℝ) ≤ wfun (y + z) := wc_423 (y + z) (by linarith) (by linarith)
                have hw5 : (171035259/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_981 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
                have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
                have hw4 : (8709539/2500000000000:ℝ) ≤ wfun (y + z) := wc_425 (y + z) (by linarith) (by linarith)
                have hw5 : (1382484427/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_984 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (32431/16384:ℝ) with hc | hc
            · rcases le_total z (17163/16384:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
                have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
                have hw4 : (28822173/10000000000000:ℝ) ≤ wfun (y + z) := wc_413 (y + z) (by linarith) (by linarith)
                have hw5 : (171035259/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_981 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
                have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
                have hw4 : (396991/125000000000:ℝ) ≤ wfun (y + z) := wc_423 (y + z) (by linarith) (by linarith)
                have hw5 : (1382484427/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_984 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (17163/16384:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
                have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
                have hw4 : (396991/125000000000:ℝ) ≤ wfun (y + z) := wc_423 (y + z) (by linarith) (by linarith)
                have hw5 : (1382484427/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_984 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
                have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
                have hw4 : (8709539/2500000000000:ℝ) ≤ wfun (y + z) := wc_425 (y + z) (by linarith) (by linarith)
                have hw5 : (174594421/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_993 (x + y + z) (by linarith) (by linarith)
                linarith

set_option maxHeartbeats 20000000 in
lemma ch_101 (x y z : ℝ) (hx1 : (2141/2048:ℝ) ≤ x) (hx2 : x ≤ (4287/4096:ℝ))
    (hy1 : (4057/2048:ℝ) ≤ y) (hy2 : y ≤ (8119/4096:ℝ))
    (hz1 : (4287/4096:ℝ) ≤ z) (hz2 : z ≤ (1073/1024:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (8569/8192:ℝ) with hc | hc
  · rcases le_total y (16233/8192:ℝ) with hc | hc
    · rcases le_total z (8579/8192:ℝ) with hc | hc
      · rcases le_total x (17133/16384:ℝ) with hc | hc
        · rcases le_total y (32461/16384:ℝ) with hc | hc
          · rcases le_total z (17153/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
              have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
              have hw4 : (41420821/10000000000000:ℝ) ≤ wfun (y + z) := wc_431 (y + z) (by linarith) (by linarith)
              have hw5 : (1382484427/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_984 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
              have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
              have hw4 : (4492441/1000000000000:ℝ) ≤ wfun (y + z) := wc_437 (y + z) (by linarith) (by linarith)
              have hw5 : (174594421/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_993 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17153/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
              have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
              have hw4 : (4492441/1000000000000:ℝ) ≤ wfun (y + z) := wc_437 (y + z) (by linarith) (by linarith)
              have hw5 : (174594421/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_993 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
              have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
              have hw4 : (6071171/1250000000000:ℝ) ≤ wfun (y + z) := wc_439 (y + z) (by linarith) (by linarith)
              have hw5 : (1411094809/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_996 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (32461/16384:ℝ) with hc | hc
          · rcases le_total z (17153/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
              have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
              have hw4 : (41420821/10000000000000:ℝ) ≤ wfun (y + z) := wc_431 (y + z) (by linarith) (by linarith)
              have hw5 : (174594421/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_993 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
              have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
              have hw4 : (4492441/1000000000000:ℝ) ≤ wfun (y + z) := wc_437 (y + z) (by linarith) (by linarith)
              have hw5 : (1411094809/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_996 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17153/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
              have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
              have hw4 : (4492441/1000000000000:ℝ) ≤ wfun (y + z) := wc_437 (y + z) (by linarith) (by linarith)
              have hw5 : (1411094809/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_996 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
              have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
              have hw4 : (6071171/1250000000000:ℝ) ≤ wfun (y + z) := wc_439 (y + z) (by linarith) (by linarith)
              have hw5 : (285100533/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1002 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (17133/16384:ℝ) with hc | hc
        · rcases le_total y (32461/16384:ℝ) with hc | hc
          · rcases le_total z (17163/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
              have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
              have hw4 : (6071171/1250000000000:ℝ) ≤ wfun (y + z) := wc_439 (y + z) (by linarith) (by linarith)
              have hw5 : (1411094809/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_996 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
              have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
              have hw4 : (26177797/5000000000000:ℝ) ≤ wfun (y + z) := wc_443 (y + z) (by linarith) (by linarith)
              have hw5 : (285100533/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1002 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17163/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
              have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
              have hw4 : (26177797/5000000000000:ℝ) ≤ wfun (y + z) := wc_443 (y + z) (by linarith) (by linarith)
              have hw5 : (285100533/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1002 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
              have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
              have hw4 : (14070747/2500000000000:ℝ) ≤ wfun (y + z) := wc_445 (y + z) (by linarith) (by linarith)
              have hw5 : (1439978849/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1005 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (32461/16384:ℝ) with hc | hc
          · rcases le_total z (17163/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
              have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
              have hw4 : (6071171/1250000000000:ℝ) ≤ wfun (y + z) := wc_439 (y + z) (by linarith) (by linarith)
              have hw5 : (285100533/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1002 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
              have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
              have hw4 : (26177797/5000000000000:ℝ) ≤ wfun (y + z) := wc_443 (y + z) (by linarith) (by linarith)
              have hw5 : (1439978849/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1005 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17163/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
              have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
              have hw4 : (26177797/5000000000000:ℝ) ≤ wfun (y + z) := wc_443 (y + z) (by linarith) (by linarith)
              have hw5 : (1439978849/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1005 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
              have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
              have hw4 : (14070747/2500000000000:ℝ) ≤ wfun (y + z) := wc_445 (y + z) (by linarith) (by linarith)
              have hw5 : (363630819/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1026 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total z (8579/8192:ℝ) with hc | hc
      · rcases le_total x (17133/16384:ℝ) with hc | hc
        · rcases le_total y (32471/16384:ℝ) with hc | hc
          · rcases le_total z (17153/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
              have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
              have hw4 : (6071171/1250000000000:ℝ) ≤ wfun (y + z) := wc_439 (y + z) (by linarith) (by linarith)
              have hw5 : (1411094809/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_996 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
              have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
              have hw4 : (26177797/5000000000000:ℝ) ≤ wfun (y + z) := wc_443 (y + z) (by linarith) (by linarith)
              have hw5 : (285100533/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1002 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17153/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
              have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
              have hw4 : (26177797/5000000000000:ℝ) ≤ wfun (y + z) := wc_443 (y + z) (by linarith) (by linarith)
              have hw5 : (285100533/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1002 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
              have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
              have hw4 : (14070747/2500000000000:ℝ) ≤ wfun (y + z) := wc_445 (y + z) (by linarith) (by linarith)
              have hw5 : (1439978849/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1005 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (32471/16384:ℝ) with hc | hc
          · rcases le_total z (17153/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
              have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
              have hw4 : (6071171/1250000000000:ℝ) ≤ wfun (y + z) := wc_439 (y + z) (by linarith) (by linarith)
              have hw5 : (285100533/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1002 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
              have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
              have hw4 : (26177797/5000000000000:ℝ) ≤ wfun (y + z) := wc_443 (y + z) (by linarith) (by linarith)
              have hw5 : (1439978849/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1005 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17153/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
              have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
              have hw4 : (26177797/5000000000000:ℝ) ≤ wfun (y + z) := wc_443 (y + z) (by linarith) (by linarith)
              have hw5 : (1439978849/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1005 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
              have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
              have hw4 : (14070747/2500000000000:ℝ) ≤ wfun (y + z) := wc_445 (y + z) (by linarith) (by linarith)
              have hw5 : (363630819/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1026 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (17133/16384:ℝ) with hc | hc
        · rcases le_total y (32471/16384:ℝ) with hc | hc
          · rcases le_total z (17163/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
              have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
              have hw4 : (14070747/2500000000000:ℝ) ≤ wfun (y + z) := wc_445 (y + z) (by linarith) (by linarith)
              have hw5 : (1439978849/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1005 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
              have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
              have hw4 : (60351447/10000000000000:ℝ) ≤ wfun (y + z) := wc_453 (y + z) (by linarith) (by linarith)
              have hw5 : (363630819/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1026 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17163/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
              have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
              have hw4 : (60351447/10000000000000:ℝ) ≤ wfun (y + z) := wc_453 (y + z) (by linarith) (by linarith)
              have hw5 : (363630819/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1026 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
              have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
              have hw4 : (16140217/2500000000000:ℝ) ≤ wfun (y + z) := wc_455 (y + z) (by linarith) (by linarith)
              have hw5 : (73456793/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1029 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (32471/16384:ℝ) with hc | hc
          · rcases le_total z (17163/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
              have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
              have hw4 : (14070747/2500000000000:ℝ) ≤ wfun (y + z) := wc_445 (y + z) (by linarith) (by linarith)
              have hw5 : (363630819/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1026 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
              have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
              have hw4 : (60351447/10000000000000:ℝ) ≤ wfun (y + z) := wc_453 (y + z) (by linarith) (by linarith)
              have hw5 : (73456793/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1029 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17163/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
              have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
              have hw4 : (60351447/10000000000000:ℝ) ≤ wfun (y + z) := wc_453 (y + z) (by linarith) (by linarith)
              have hw5 : (73456793/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1029 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
              have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
              have hw4 : (16140217/2500000000000:ℝ) ≤ wfun (y + z) := wc_455 (y + z) (by linarith) (by linarith)
              have hw5 : (296763303/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1035 (x + y + z) (by linarith) (by linarith)
              linarith
  · rcases le_total y (16233/8192:ℝ) with hc | hc
    · rcases le_total z (8579/8192:ℝ) with hc | hc
      · rcases le_total x (17143/16384:ℝ) with hc | hc
        · rcases le_total y (32461/16384:ℝ) with hc | hc
          · rcases le_total z (17153/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
              have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
              have hw4 : (41420821/10000000000000:ℝ) ≤ wfun (y + z) := wc_431 (y + z) (by linarith) (by linarith)
              have hw5 : (1411094809/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_996 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
              have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
              have hw4 : (4492441/1000000000000:ℝ) ≤ wfun (y + z) := wc_437 (y + z) (by linarith) (by linarith)
              have hw5 : (285100533/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1002 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17153/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
              have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
              have hw4 : (4492441/1000000000000:ℝ) ≤ wfun (y + z) := wc_437 (y + z) (by linarith) (by linarith)
              have hw5 : (285100533/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1002 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
              have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
              have hw4 : (6071171/1250000000000:ℝ) ≤ wfun (y + z) := wc_439 (y + z) (by linarith) (by linarith)
              have hw5 : (1439978849/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1005 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (32461/16384:ℝ) with hc | hc
          · rcases le_total z (17153/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
              have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
              have hw4 : (41420821/10000000000000:ℝ) ≤ wfun (y + z) := wc_431 (y + z) (by linarith) (by linarith)
              have hw5 : (285100533/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1002 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
              have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
              have hw4 : (4492441/1000000000000:ℝ) ≤ wfun (y + z) := wc_437 (y + z) (by linarith) (by linarith)
              have hw5 : (1439978849/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1005 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17153/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
              have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
              have hw4 : (4492441/1000000000000:ℝ) ≤ wfun (y + z) := wc_437 (y + z) (by linarith) (by linarith)
              have hw5 : (1439978849/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1005 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
              have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
              have hw4 : (6071171/1250000000000:ℝ) ≤ wfun (y + z) := wc_439 (y + z) (by linarith) (by linarith)
              have hw5 : (363630819/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1026 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (17143/16384:ℝ) with hc | hc
        · rcases le_total y (32461/16384:ℝ) with hc | hc
          · rcases le_total z (17163/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
              have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
              have hw4 : (6071171/1250000000000:ℝ) ≤ wfun (y + z) := wc_439 (y + z) (by linarith) (by linarith)
              have hw5 : (1439978849/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1005 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
              have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
              have hw4 : (26177797/5000000000000:ℝ) ≤ wfun (y + z) := wc_443 (y + z) (by linarith) (by linarith)
              have hw5 : (363630819/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1026 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17163/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
              have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
              have hw4 : (26177797/5000000000000:ℝ) ≤ wfun (y + z) := wc_443 (y + z) (by linarith) (by linarith)
              have hw5 : (363630819/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1026 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
              have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
              have hw4 : (14070747/2500000000000:ℝ) ≤ wfun (y + z) := wc_445 (y + z) (by linarith) (by linarith)
              have hw5 : (73456793/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1029 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (32461/16384:ℝ) with hc | hc
          · rcases le_total z (17163/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
              have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
              have hw4 : (6071171/1250000000000:ℝ) ≤ wfun (y + z) := wc_439 (y + z) (by linarith) (by linarith)
              have hw5 : (363630819/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1026 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
              have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
              have hw4 : (26177797/5000000000000:ℝ) ≤ wfun (y + z) := wc_443 (y + z) (by linarith) (by linarith)
              have hw5 : (73456793/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1029 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17163/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
              have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
              have hw4 : (26177797/5000000000000:ℝ) ≤ wfun (y + z) := wc_443 (y + z) (by linarith) (by linarith)
              have hw5 : (73456793/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1029 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
              have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
              have hw4 : (14070747/2500000000000:ℝ) ≤ wfun (y + z) := wc_445 (y + z) (by linarith) (by linarith)
              have hw5 : (296763303/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1035 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total z (8579/8192:ℝ) with hc | hc
      · rcases le_total x (17143/16384:ℝ) with hc | hc
        · rcases le_total y (32471/16384:ℝ) with hc | hc
          · rcases le_total z (17153/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
              have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
              have hw4 : (6071171/1250000000000:ℝ) ≤ wfun (y + z) := wc_439 (y + z) (by linarith) (by linarith)
              have hw5 : (1439978849/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1005 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
              have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
              have hw4 : (26177797/5000000000000:ℝ) ≤ wfun (y + z) := wc_443 (y + z) (by linarith) (by linarith)
              have hw5 : (363630819/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1026 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17153/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
              have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
              have hw4 : (26177797/5000000000000:ℝ) ≤ wfun (y + z) := wc_443 (y + z) (by linarith) (by linarith)
              have hw5 : (363630819/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1026 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
              have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
              have hw4 : (14070747/2500000000000:ℝ) ≤ wfun (y + z) := wc_445 (y + z) (by linarith) (by linarith)
              have hw5 : (73456793/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1029 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (32471/16384:ℝ) with hc | hc
          · rcases le_total z (17153/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
              have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
              have hw4 : (6071171/1250000000000:ℝ) ≤ wfun (y + z) := wc_439 (y + z) (by linarith) (by linarith)
              have hw5 : (363630819/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1026 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
              have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
              have hw4 : (26177797/5000000000000:ℝ) ≤ wfun (y + z) := wc_443 (y + z) (by linarith) (by linarith)
              have hw5 : (73456793/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1029 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17153/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
              have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
              have hw4 : (26177797/5000000000000:ℝ) ≤ wfun (y + z) := wc_443 (y + z) (by linarith) (by linarith)
              have hw5 : (73456793/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1029 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
              have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
              have hw4 : (14070747/2500000000000:ℝ) ≤ wfun (y + z) := wc_445 (y + z) (by linarith) (by linarith)
              have hw5 : (296763303/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1035 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (17143/16384:ℝ) with hc | hc
        · rcases le_total y (32471/16384:ℝ) with hc | hc
          · rcases le_total z (17163/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
              have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
              have hw4 : (14070747/2500000000000:ℝ) ≤ wfun (y + z) := wc_445 (y + z) (by linarith) (by linarith)
              have hw5 : (73456793/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1029 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
              have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
              have hw4 : (60351447/10000000000000:ℝ) ≤ wfun (y + z) := wc_453 (y + z) (by linarith) (by linarith)
              have hw5 : (296763303/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1035 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17163/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
              have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
              have hw4 : (60351447/10000000000000:ℝ) ≤ wfun (y + z) := wc_453 (y + z) (by linarith) (by linarith)
              have hw5 : (296763303/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1035 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
              have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
              have hw4 : (16140217/2500000000000:ℝ) ≤ wfun (y + z) := wc_455 (y + z) (by linarith) (by linarith)
              have hw5 : (1498565153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1038 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (32471/16384:ℝ) with hc | hc
          · rcases le_total z (17163/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
              have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
              have hw4 : (14070747/2500000000000:ℝ) ≤ wfun (y + z) := wc_445 (y + z) (by linarith) (by linarith)
              have hw5 : (296763303/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1035 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
              have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
              have hw4 : (60351447/10000000000000:ℝ) ≤ wfun (y + z) := wc_453 (y + z) (by linarith) (by linarith)
              have hw5 : (1498565153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1038 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17163/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
              have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
              have hw4 : (60351447/10000000000000:ℝ) ≤ wfun (y + z) := wc_453 (y + z) (by linarith) (by linarith)
              have hw5 : (1498565153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1038 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
              have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
              have hw4 : (16140217/2500000000000:ℝ) ≤ wfun (y + z) := wc_455 (y + z) (by linarith) (by linarith)
              have hw5 : (189172711/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1047 (x + y + z) (by linarith) (by linarith)
              linarith

set_option maxHeartbeats 20000000 in
lemma ch_105 (x y z : ℝ) (hx1 : (4287/4096:ℝ) ≤ x) (hx2 : x ≤ (1073/1024:ℝ))
    (hy1 : (4057/2048:ℝ) ≤ y) (hy2 : y ≤ (8119/4096:ℝ))
    (hz1 : (4287/4096:ℝ) ≤ z) (hz2 : z ≤ (1073/1024:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (8579/8192:ℝ) with hc | hc
  · rcases le_total y (16233/8192:ℝ) with hc | hc
    · rcases le_total z (8579/8192:ℝ) with hc | hc
      · rcases le_total x (17153/16384:ℝ) with hc | hc
        · rcases le_total y (32461/16384:ℝ) with hc | hc
          · rcases le_total z (17153/16384:ℝ) with hc | hc
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
              have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
              have hw4 : (41420821/10000000000000:ℝ) ≤ wfun (y + z) := wc_431 (y + z) (by linarith) (by linarith)
              have hw5 : (1439978849/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1005 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
              have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
              have hw4 : (4492441/1000000000000:ℝ) ≤ wfun (y + z) := wc_437 (y + z) (by linarith) (by linarith)
              have hw5 : (363630819/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1026 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17153/16384:ℝ) with hc | hc
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
              have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
              have hw4 : (4492441/1000000000000:ℝ) ≤ wfun (y + z) := wc_437 (y + z) (by linarith) (by linarith)
              have hw5 : (363630819/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1026 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
              have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
              have hw4 : (6071171/1250000000000:ℝ) ≤ wfun (y + z) := wc_439 (y + z) (by linarith) (by linarith)
              have hw5 : (73456793/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1029 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (32461/16384:ℝ) with hc | hc
          · rcases le_total z (17153/16384:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
              have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
              have hw4 : (41420821/10000000000000:ℝ) ≤ wfun (y + z) := wc_431 (y + z) (by linarith) (by linarith)
              have hw5 : (363630819/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1026 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
              have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
              have hw4 : (4492441/1000000000000:ℝ) ≤ wfun (y + z) := wc_437 (y + z) (by linarith) (by linarith)
              have hw5 : (73456793/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1029 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17153/16384:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
              have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
              have hw4 : (4492441/1000000000000:ℝ) ≤ wfun (y + z) := wc_437 (y + z) (by linarith) (by linarith)
              have hw5 : (73456793/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1029 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
              have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
              have hw4 : (6071171/1250000000000:ℝ) ≤ wfun (y + z) := wc_439 (y + z) (by linarith) (by linarith)
              have hw5 : (296763303/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1035 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (17153/16384:ℝ) with hc | hc
        · rcases le_total y (32461/16384:ℝ) with hc | hc
          · rcases le_total z (17163/16384:ℝ) with hc | hc
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
              have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
              have hw4 : (6071171/1250000000000:ℝ) ≤ wfun (y + z) := wc_439 (y + z) (by linarith) (by linarith)
              have hw5 : (73456793/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1029 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
              have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
              have hw4 : (26177797/5000000000000:ℝ) ≤ wfun (y + z) := wc_443 (y + z) (by linarith) (by linarith)
              have hw5 : (296763303/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1035 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17163/16384:ℝ) with hc | hc
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
              have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
              have hw4 : (26177797/5000000000000:ℝ) ≤ wfun (y + z) := wc_443 (y + z) (by linarith) (by linarith)
              have hw5 : (296763303/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1035 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
              have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
              have hw4 : (14070747/2500000000000:ℝ) ≤ wfun (y + z) := wc_445 (y + z) (by linarith) (by linarith)
              have hw5 : (1498565153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1038 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (32461/16384:ℝ) with hc | hc
          · rcases le_total z (17163/16384:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
              have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
              have hw4 : (6071171/1250000000000:ℝ) ≤ wfun (y + z) := wc_439 (y + z) (by linarith) (by linarith)
              have hw5 : (296763303/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1035 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
              have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
              have hw4 : (26177797/5000000000000:ℝ) ≤ wfun (y + z) := wc_443 (y + z) (by linarith) (by linarith)
              have hw5 : (1498565153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1038 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17163/16384:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
              have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
              have hw4 : (26177797/5000000000000:ℝ) ≤ wfun (y + z) := wc_443 (y + z) (by linarith) (by linarith)
              have hw5 : (1498565153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1038 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
              have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
              have hw4 : (14070747/2500000000000:ℝ) ≤ wfun (y + z) := wc_445 (y + z) (by linarith) (by linarith)
              have hw5 : (189172711/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1047 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total z (8579/8192:ℝ) with hc | hc
      · rcases le_total x (17153/16384:ℝ) with hc | hc
        · rcases le_total y (32471/16384:ℝ) with hc | hc
          · rcases le_total z (17153/16384:ℝ) with hc | hc
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
              have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
              have hw4 : (6071171/1250000000000:ℝ) ≤ wfun (y + z) := wc_439 (y + z) (by linarith) (by linarith)
              have hw5 : (73456793/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1029 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
              have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
              have hw4 : (26177797/5000000000000:ℝ) ≤ wfun (y + z) := wc_443 (y + z) (by linarith) (by linarith)
              have hw5 : (296763303/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1035 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17153/16384:ℝ) with hc | hc
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
              have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
              have hw4 : (26177797/5000000000000:ℝ) ≤ wfun (y + z) := wc_443 (y + z) (by linarith) (by linarith)
              have hw5 : (296763303/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1035 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
              have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
              have hw4 : (14070747/2500000000000:ℝ) ≤ wfun (y + z) := wc_445 (y + z) (by linarith) (by linarith)
              have hw5 : (1498565153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1038 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (32471/16384:ℝ) with hc | hc
          · rcases le_total z (17153/16384:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
              have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
              have hw4 : (6071171/1250000000000:ℝ) ≤ wfun (y + z) := wc_439 (y + z) (by linarith) (by linarith)
              have hw5 : (296763303/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1035 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
              have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
              have hw4 : (26177797/5000000000000:ℝ) ≤ wfun (y + z) := wc_443 (y + z) (by linarith) (by linarith)
              have hw5 : (1498565153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1038 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17153/16384:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
              have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
              have hw4 : (26177797/5000000000000:ℝ) ≤ wfun (y + z) := wc_443 (y + z) (by linarith) (by linarith)
              have hw5 : (1498565153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1038 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
              have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
              have hw4 : (14070747/2500000000000:ℝ) ≤ wfun (y + z) := wc_445 (y + z) (by linarith) (by linarith)
              have hw5 : (189172711/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1047 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (17153/16384:ℝ) with hc | hc
        · rcases le_total y (32471/16384:ℝ) with hc | hc
          · rcases le_total z (17163/16384:ℝ) with hc | hc
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
              have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
              have hw4 : (14070747/2500000000000:ℝ) ≤ wfun (y + z) := wc_445 (y + z) (by linarith) (by linarith)
              have hw5 : (1498565153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1038 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
              have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
              have hw4 : (60351447/10000000000000:ℝ) ≤ wfun (y + z) := wc_453 (y + z) (by linarith) (by linarith)
              have hw5 : (189172711/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1047 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17163/16384:ℝ) with hc | hc
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
              have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
              have hw4 : (60351447/10000000000000:ℝ) ≤ wfun (y + z) := wc_453 (y + z) (by linarith) (by linarith)
              have hw5 : (189172711/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1047 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
              have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
              have hw4 : (16140217/2500000000000:ℝ) ≤ wfun (y + z) := wc_455 (y + z) (by linarith) (by linarith)
              have hw5 : (1528266033/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1050 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (32471/16384:ℝ) with hc | hc
          · rcases le_total z (17163/16384:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
              have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
              have hw4 : (14070747/2500000000000:ℝ) ≤ wfun (y + z) := wc_445 (y + z) (by linarith) (by linarith)
              have hw5 : (189172711/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1047 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
              have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
              have hw4 : (60351447/10000000000000:ℝ) ≤ wfun (y + z) := wc_453 (y + z) (by linarith) (by linarith)
              have hw5 : (1528266033/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1050 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17163/16384:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
              have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
              have hw4 : (60351447/10000000000000:ℝ) ≤ wfun (y + z) := wc_453 (y + z) (by linarith) (by linarith)
              have hw5 : (1528266033/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1050 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
              have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
              have hw4 : (16140217/2500000000000:ℝ) ≤ wfun (y + z) := wc_455 (y + z) (by linarith) (by linarith)
              have hw5 : (15432181/100000000000:ℝ) ≤ wfun (x + y + z) := wc_1056 (x + y + z) (by linarith) (by linarith)
              linarith
  · rcases le_total y (16233/8192:ℝ) with hc | hc
    · rcases le_total z (8579/8192:ℝ) with hc | hc
      · rcases le_total x (17163/16384:ℝ) with hc | hc
        · rcases le_total y (32461/16384:ℝ) with hc | hc
          · rcases le_total z (17153/16384:ℝ) with hc | hc
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
              have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
              have hw4 : (41420821/10000000000000:ℝ) ≤ wfun (y + z) := wc_431 (y + z) (by linarith) (by linarith)
              have hw5 : (73456793/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1029 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
              have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
              have hw4 : (4492441/1000000000000:ℝ) ≤ wfun (y + z) := wc_437 (y + z) (by linarith) (by linarith)
              have hw5 : (296763303/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1035 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17153/16384:ℝ) with hc | hc
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
              have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
              have hw4 : (4492441/1000000000000:ℝ) ≤ wfun (y + z) := wc_437 (y + z) (by linarith) (by linarith)
              have hw5 : (296763303/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1035 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
              have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
              have hw4 : (6071171/1250000000000:ℝ) ≤ wfun (y + z) := wc_439 (y + z) (by linarith) (by linarith)
              have hw5 : (1498565153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1038 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (32461/16384:ℝ) with hc | hc
          · rcases le_total z (17153/16384:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
              have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
              have hw4 : (41420821/10000000000000:ℝ) ≤ wfun (y + z) := wc_431 (y + z) (by linarith) (by linarith)
              have hw5 : (296763303/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1035 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
              have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
              have hw4 : (4492441/1000000000000:ℝ) ≤ wfun (y + z) := wc_437 (y + z) (by linarith) (by linarith)
              have hw5 : (1498565153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1038 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17153/16384:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
              have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
              have hw4 : (4492441/1000000000000:ℝ) ≤ wfun (y + z) := wc_437 (y + z) (by linarith) (by linarith)
              have hw5 : (1498565153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1038 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
              have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
              have hw4 : (6071171/1250000000000:ℝ) ≤ wfun (y + z) := wc_439 (y + z) (by linarith) (by linarith)
              have hw5 : (189172711/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1047 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (17163/16384:ℝ) with hc | hc
        · rcases le_total y (32461/16384:ℝ) with hc | hc
          · rcases le_total z (17163/16384:ℝ) with hc | hc
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
              have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
              have hw4 : (6071171/1250000000000:ℝ) ≤ wfun (y + z) := wc_439 (y + z) (by linarith) (by linarith)
              have hw5 : (1498565153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1038 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
              have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
              have hw4 : (26177797/5000000000000:ℝ) ≤ wfun (y + z) := wc_443 (y + z) (by linarith) (by linarith)
              have hw5 : (189172711/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1047 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17163/16384:ℝ) with hc | hc
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
              have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
              have hw4 : (26177797/5000000000000:ℝ) ≤ wfun (y + z) := wc_443 (y + z) (by linarith) (by linarith)
              have hw5 : (189172711/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1047 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
              have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
              have hw4 : (14070747/2500000000000:ℝ) ≤ wfun (y + z) := wc_445 (y + z) (by linarith) (by linarith)
              have hw5 : (1528266033/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1050 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (32461/16384:ℝ) with hc | hc
          · rcases le_total z (17163/16384:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
              have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
              have hw4 : (6071171/1250000000000:ℝ) ≤ wfun (y + z) := wc_439 (y + z) (by linarith) (by linarith)
              have hw5 : (189172711/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1047 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
              have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
              have hw4 : (26177797/5000000000000:ℝ) ≤ wfun (y + z) := wc_443 (y + z) (by linarith) (by linarith)
              have hw5 : (1528266033/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1050 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17163/16384:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
              have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
              have hw4 : (26177797/5000000000000:ℝ) ≤ wfun (y + z) := wc_443 (y + z) (by linarith) (by linarith)
              have hw5 : (1528266033/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1050 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
              have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
              have hw4 : (14070747/2500000000000:ℝ) ≤ wfun (y + z) := wc_445 (y + z) (by linarith) (by linarith)
              have hw5 : (15432181/100000000000:ℝ) ≤ wfun (x + y + z) := wc_1056 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total z (8579/8192:ℝ) with hc | hc
      · rcases le_total x (17163/16384:ℝ) with hc | hc
        · rcases le_total y (32471/16384:ℝ) with hc | hc
          · rcases le_total z (17153/16384:ℝ) with hc | hc
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
              have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
              have hw4 : (6071171/1250000000000:ℝ) ≤ wfun (y + z) := wc_439 (y + z) (by linarith) (by linarith)
              have hw5 : (1498565153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1038 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
              have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
              have hw4 : (26177797/5000000000000:ℝ) ≤ wfun (y + z) := wc_443 (y + z) (by linarith) (by linarith)
              have hw5 : (189172711/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1047 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17153/16384:ℝ) with hc | hc
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
              have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
              have hw4 : (26177797/5000000000000:ℝ) ≤ wfun (y + z) := wc_443 (y + z) (by linarith) (by linarith)
              have hw5 : (189172711/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1047 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
              have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
              have hw4 : (14070747/2500000000000:ℝ) ≤ wfun (y + z) := wc_445 (y + z) (by linarith) (by linarith)
              have hw5 : (1528266033/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1050 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (32471/16384:ℝ) with hc | hc
          · rcases le_total z (17153/16384:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
              have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
              have hw4 : (6071171/1250000000000:ℝ) ≤ wfun (y + z) := wc_439 (y + z) (by linarith) (by linarith)
              have hw5 : (189172711/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1047 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
              have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
              have hw4 : (26177797/5000000000000:ℝ) ≤ wfun (y + z) := wc_443 (y + z) (by linarith) (by linarith)
              have hw5 : (1528266033/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1050 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17153/16384:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
              have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
              have hw4 : (26177797/5000000000000:ℝ) ≤ wfun (y + z) := wc_443 (y + z) (by linarith) (by linarith)
              have hw5 : (1528266033/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1050 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
              have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
              have hw4 : (14070747/2500000000000:ℝ) ≤ wfun (y + z) := wc_445 (y + z) (by linarith) (by linarith)
              have hw5 : (15432181/100000000000:ℝ) ≤ wfun (x + y + z) := wc_1056 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (17163/16384:ℝ) with hc | hc
        · rcases le_total y (32471/16384:ℝ) with hc | hc
          · rcases le_total z (17163/16384:ℝ) with hc | hc
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
              have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
              have hw4 : (14070747/2500000000000:ℝ) ≤ wfun (y + z) := wc_445 (y + z) (by linarith) (by linarith)
              have hw5 : (1528266033/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1050 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
              have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
              have hw4 : (60351447/10000000000000:ℝ) ≤ wfun (y + z) := wc_453 (y + z) (by linarith) (by linarith)
              have hw5 : (15432181/100000000000:ℝ) ≤ wfun (x + y + z) := wc_1056 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17163/16384:ℝ) with hc | hc
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
              have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
              have hw4 : (60351447/10000000000000:ℝ) ≤ wfun (y + z) := wc_453 (y + z) (by linarith) (by linarith)
              have hw5 : (15432181/100000000000:ℝ) ≤ wfun (x + y + z) := wc_1056 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
              have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
              have hw4 : (16140217/2500000000000:ℝ) ≤ wfun (y + z) := wc_455 (y + z) (by linarith) (by linarith)
              have hw5 : (7791189/50000000000:ℝ) ≤ wfun (x + y + z) := wc_1059 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (32471/16384:ℝ) with hc | hc
          · rcases le_total z (17163/16384:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
              have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
              have hw4 : (14070747/2500000000000:ℝ) ≤ wfun (y + z) := wc_445 (y + z) (by linarith) (by linarith)
              have hw5 : (15432181/100000000000:ℝ) ≤ wfun (x + y + z) := wc_1056 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
              have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
              have hw4 : (60351447/10000000000000:ℝ) ≤ wfun (y + z) := wc_453 (y + z) (by linarith) (by linarith)
              have hw5 : (7791189/50000000000:ℝ) ≤ wfun (x + y + z) := wc_1059 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
            have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
            have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
            have hw4 : (30163501/5000000000000:ℝ) ≤ wfun (y + z) := wc_454 (y + z) (by linarith) (by linarith)
            have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
            linarith

set_option maxHeartbeats 20000000 in
lemma ch_118 (x y z : ℝ) (hx1 : (4287/4096:ℝ) ≤ x) (hx2 : x ≤ (1073/1024:ℝ))
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
    · rcases le_total x (8579/8192:ℝ) with hc | hc
      · rcases le_total y (16233/8192:ℝ) with hc | hc
        · rcases le_total z (8589/8192:ℝ) with hc | hc
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · rcases le_total y (32461/16384:ℝ) with hc | hc
              · rcases le_total z (17173/16384:ℝ) with hc | hc
                · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                  have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                  have hw2 : (653599921/10000000000000:ℝ) ≤ wfun z := wc_68 z (by linarith) (by linarith)
                  have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
                  have hw4 : (14070747/2500000000000:ℝ) ≤ wfun (y + z) := wc_445 (y + z) (by linarith) (by linarith)
                  have hw5 : (1498565153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1038 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                  have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_73 z (by linarith) (by linarith)
                  have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
                  have hw4 : (60351447/10000000000000:ℝ) ≤ wfun (y + z) := wc_453 (y + z) (by linarith) (by linarith)
                  have hw5 : (189172711/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1047 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (17173/16384:ℝ) with hc | hc
                · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                  have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                  have hw2 : (653599921/10000000000000:ℝ) ≤ wfun z := wc_68 z (by linarith) (by linarith)
                  have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
                  have hw4 : (60351447/10000000000000:ℝ) ≤ wfun (y + z) := wc_453 (y + z) (by linarith) (by linarith)
                  have hw5 : (189172711/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1047 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                  have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_73 z (by linarith) (by linarith)
                  have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
                  have hw4 : (16140217/2500000000000:ℝ) ≤ wfun (y + z) := wc_455 (y + z) (by linarith) (by linarith)
                  have hw5 : (1528266033/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1050 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total y (32461/16384:ℝ) with hc | hc
              · rcases le_total z (17173/16384:ℝ) with hc | hc
                · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                  have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                  have hw2 : (653599921/10000000000000:ℝ) ≤ wfun z := wc_68 z (by linarith) (by linarith)
                  have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
                  have hw4 : (14070747/2500000000000:ℝ) ≤ wfun (y + z) := wc_445 (y + z) (by linarith) (by linarith)
                  have hw5 : (189172711/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1047 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                  have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_73 z (by linarith) (by linarith)
                  have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
                  have hw4 : (60351447/10000000000000:ℝ) ≤ wfun (y + z) := wc_453 (y + z) (by linarith) (by linarith)
                  have hw5 : (1528266033/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1050 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (17173/16384:ℝ) with hc | hc
                · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                  have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                  have hw2 : (653599921/10000000000000:ℝ) ≤ wfun z := wc_68 z (by linarith) (by linarith)
                  have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
                  have hw4 : (60351447/10000000000000:ℝ) ≤ wfun (y + z) := wc_453 (y + z) (by linarith) (by linarith)
                  have hw5 : (1528266033/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1050 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                  have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_73 z (by linarith) (by linarith)
                  have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
                  have hw4 : (16140217/2500000000000:ℝ) ≤ wfun (y + z) := wc_455 (y + z) (by linarith) (by linarith)
                  have hw5 : (15432181/100000000000:ℝ) ≤ wfun (x + y + z) := wc_1056 (x + y + z) (by linarith) (by linarith)
                  linarith
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · rcases le_total y (32461/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
                have hw4 : (64534721/10000000000000:ℝ) ≤ wfun (y + z) := wc_456 (y + z) (by linarith) (by linarith)
                have hw5 : (305561427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1051 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
                have hw4 : (68883243/10000000000000:ℝ) ≤ wfun (y + z) := wc_460 (y + z) (by linarith) (by linarith)
                have hw5 : (1542754747/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1057 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32461/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
                have hw4 : (64534721/10000000000000:ℝ) ≤ wfun (y + z) := wc_456 (y + z) (by linarith) (by linarith)
                have hw5 : (1542754747/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1057 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
                have hw4 : (68883243/10000000000000:ℝ) ≤ wfun (y + z) := wc_460 (y + z) (by linarith) (by linarith)
                have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (8589/8192:ℝ) with hc | hc
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · rcases le_total y (32471/16384:ℝ) with hc | hc
              · rcases le_total z (17173/16384:ℝ) with hc | hc
                · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                  have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                  have hw2 : (653599921/10000000000000:ℝ) ≤ wfun z := wc_68 z (by linarith) (by linarith)
                  have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
                  have hw4 : (16140217/2500000000000:ℝ) ≤ wfun (y + z) := wc_455 (y + z) (by linarith) (by linarith)
                  have hw5 : (1528266033/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1050 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                  have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_73 z (by linarith) (by linarith)
                  have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
                  have hw4 : (68911149/10000000000000:ℝ) ≤ wfun (y + z) := wc_459 (y + z) (by linarith) (by linarith)
                  have hw5 : (15432181/100000000000:ℝ) ≤ wfun (x + y + z) := wc_1056 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
                have hw4 : (68883243/10000000000000:ℝ) ≤ wfun (y + z) := wc_460 (y + z) (by linarith) (by linarith)
                have hw5 : (1542754747/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1057 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32471/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
                have hw4 : (64534721/10000000000000:ℝ) ≤ wfun (y + z) := wc_456 (y + z) (by linarith) (by linarith)
                have hw5 : (1542754747/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1057 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
                have hw4 : (68883243/10000000000000:ℝ) ≤ wfun (y + z) := wc_460 (y + z) (by linarith) (by linarith)
                have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · rcases le_total y (32471/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
                have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
                have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
                have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
                have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32471/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
                have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
                have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
                have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
                have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total y (16233/8192:ℝ) with hc | hc
        · rcases le_total z (8589/8192:ℝ) with hc | hc
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · rcases le_total y (32461/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
                have hw4 : (56260189/10000000000000:ℝ) ≤ wfun (y + z) := wc_446 (y + z) (by linarith) (by linarith)
                have hw5 : (305561427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1051 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
                have hw4 : (30163501/5000000000000:ℝ) ≤ wfun (y + z) := wc_454 (y + z) (by linarith) (by linarith)
                have hw5 : (1542754747/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1057 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32461/16384:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
                have hw4 : (56260189/10000000000000:ℝ) ≤ wfun (y + z) := wc_446 (y + z) (by linarith) (by linarith)
                have hw5 : (1542754747/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1057 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
                have hw4 : (30163501/5000000000000:ℝ) ≤ wfun (y + z) := wc_454 (y + z) (by linarith) (by linarith)
                have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · rcases le_total y (32461/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
                have hw4 : (64534721/10000000000000:ℝ) ≤ wfun (y + z) := wc_456 (y + z) (by linarith) (by linarith)
                have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
                have hw4 : (68883243/10000000000000:ℝ) ≤ wfun (y + z) := wc_460 (y + z) (by linarith) (by linarith)
                have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32461/16384:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
                have hw4 : (64534721/10000000000000:ℝ) ≤ wfun (y + z) := wc_456 (y + z) (by linarith) (by linarith)
                have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
                have hw4 : (68883243/10000000000000:ℝ) ≤ wfun (y + z) := wc_460 (y + z) (by linarith) (by linarith)
                have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (8589/8192:ℝ) with hc | hc
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · rcases le_total y (32471/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
                have hw4 : (64534721/10000000000000:ℝ) ≤ wfun (y + z) := wc_456 (y + z) (by linarith) (by linarith)
                have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (68883243/10000000000000:ℝ) ≤ wfun (y + z) := wc_460 (y + z) (by linarith) (by linarith)
                have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32471/16384:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (64534721/10000000000000:ℝ) ≤ wfun (y + z) := wc_456 (y + z) (by linarith) (by linarith)
                have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (68883243/10000000000000:ℝ) ≤ wfun (y + z) := wc_460 (y + z) (by linarith) (by linarith)
                have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · rcases le_total y (32471/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
                have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
                have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
                have hw5 : (1603220471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1079 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32471/16384:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
                have hw5 : (1603220471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1079 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
                have hw5 : (1618505281/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1081 (x + y + z) (by linarith) (by linarith)
                linarith
    · rcases le_total x (8579/8192:ℝ) with hc | hc
      · rcases le_total y (16233/8192:ℝ) with hc | hc
        · rcases le_total z (8599/8192:ℝ) with hc | hc
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · rcases le_total y (32461/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
                have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
                have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
                have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
                have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32461/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
                have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
                have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
                have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
                have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (10351009/2500000000000:ℝ) ≤ wfun (x + y) := wc_432 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (396881567/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1075 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (22453103/5000000000000:ℝ) ≤ wfun (x + y) := wc_438 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (1602739283/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1080 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (8599/8192:ℝ) with hc | hc
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · rcases le_total y (32471/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
                have hw4 : (8277259/1000000000000:ℝ) ≤ wfun (y + z) := wc_470 (y + z) (by linarith) (by linarith)
                have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
                have hw4 : (17536657/2000000000000:ℝ) ≤ wfun (y + z) := wc_474 (y + z) (by linarith) (by linarith)
                have hw5 : (1603220471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1079 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (3270899/625000000000:ℝ) ≤ wfun (x + y) := wc_444 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (1602739283/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1080 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (48549689/10000000000000:ℝ) ≤ wfun (x + y) := wc_440 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (1618019543/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1082 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (3270899/625000000000:ℝ) ≤ wfun (x + y) := wc_444 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (1633366957/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1090 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total y (16233/8192:ℝ) with hc | hc
        · rcases le_total z (8599/8192:ℝ) with hc | hc
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · rcases le_total y (32461/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
                have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
                have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
                have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
                have hw5 : (1603220471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1079 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (3270899/625000000000:ℝ) ≤ wfun (x + y) := wc_444 (x + y) (by linarith) (by linarith)
              have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
              have hw5 : (1602739283/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1080 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (48549689/10000000000000:ℝ) ≤ wfun (x + y) := wc_440 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (1618019543/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1082 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (3270899/625000000000:ℝ) ≤ wfun (x + y) := wc_444 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (1633366957/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1090 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (8599/8192:ℝ) with hc | hc
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (56260189/10000000000000:ℝ) ≤ wfun (x + y) := wc_446 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (1618019543/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1082 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (30163501/5000000000000:ℝ) ≤ wfun (x + y) := wc_454 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (1633366957/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1090 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
            have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
            have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
            have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
            have hw5 : (65931469/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1093 (x + y + z) (by linarith) (by linarith)
            linarith
  · rcases le_total z (4297/4096:ℝ) with hc | hc
    · rcases le_total x (8579/8192:ℝ) with hc | hc
      · rcases le_total y (16243/8192:ℝ) with hc | hc
        · rcases le_total z (8589/8192:ℝ) with hc | hc
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · rcases le_total y (32481/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
                have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
                have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
                have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32481/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
                have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
                have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · rcases le_total y (32481/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
                have hw4 : (8277259/1000000000000:ℝ) ≤ wfun (y + z) := wc_470 (y + z) (by linarith) (by linarith)
                have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (17536657/2000000000000:ℝ) ≤ wfun (y + z) := wc_474 (y + z) (by linarith) (by linarith)
                have hw5 : (1603220471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1079 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32481/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (8277259/1000000000000:ℝ) ≤ wfun (y + z) := wc_470 (y + z) (by linarith) (by linarith)
                have hw5 : (1603220471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1079 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (17536657/2000000000000:ℝ) ≤ wfun (y + z) := wc_474 (y + z) (by linarith) (by linarith)
                have hw5 : (1618505281/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1081 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (8589/8192:ℝ) with hc | hc
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · rcases le_total y (32491/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (8277259/1000000000000:ℝ) ≤ wfun (y + z) := wc_470 (y + z) (by linarith) (by linarith)
                have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                have hw4 : (17536657/2000000000000:ℝ) ≤ wfun (y + z) := wc_474 (y + z) (by linarith) (by linarith)
                have hw5 : (1603220471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1079 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32491/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                have hw4 : (8277259/1000000000000:ℝ) ≤ wfun (y + z) := wc_470 (y + z) (by linarith) (by linarith)
                have hw5 : (1603220471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1079 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
                have hw4 : (17536657/2000000000000:ℝ) ≤ wfun (y + z) := wc_474 (y + z) (by linarith) (by linarith)
                have hw5 : (1618505281/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1081 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · rcases le_total y (32491/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (92734261/10000000000000:ℝ) ≤ wfun (y + z) := wc_476 (y + z) (by linarith) (by linarith)
                have hw5 : (1618505281/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1081 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                have hw4 : (97925413/10000000000000:ℝ) ≤ wfun (y + z) := wc_495 (y + z) (by linarith) (by linarith)
                have hw5 : (816928633/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1089 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32491/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                have hw4 : (92734261/10000000000000:ℝ) ≤ wfun (y + z) := wc_476 (y + z) (by linarith) (by linarith)
                have hw5 : (816928633/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1089 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
                have hw4 : (97925413/10000000000000:ℝ) ≤ wfun (y + z) := wc_495 (y + z) (by linarith) (by linarith)
                have hw5 : (1649276337/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1091 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total y (16243/8192:ℝ) with hc | hc
        · rcases le_total z (8589/8192:ℝ) with hc | hc
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · rcases le_total y (32481/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
                have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
                have hw5 : (1603220471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1079 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32481/16384:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
                have hw5 : (1603220471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1079 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
                have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
                have hw5 : (1618505281/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1081 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · rcases le_total y (32481/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (8277259/1000000000000:ℝ) ≤ wfun (y + z) := wc_470 (y + z) (by linarith) (by linarith)
                have hw5 : (1618505281/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1081 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                have hw4 : (17536657/2000000000000:ℝ) ≤ wfun (y + z) := wc_474 (y + z) (by linarith) (by linarith)
                have hw5 : (816928633/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1089 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32481/16384:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                have hw4 : (8277259/1000000000000:ℝ) ≤ wfun (y + z) := wc_470 (y + z) (by linarith) (by linarith)
                have hw5 : (816928633/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1089 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
                have hw4 : (17536657/2000000000000:ℝ) ≤ wfun (y + z) := wc_474 (y + z) (by linarith) (by linarith)
                have hw5 : (1649276337/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1091 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (8589/8192:ℝ) with hc | hc
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · rcases le_total y (32491/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
                have hw4 : (8277259/1000000000000:ℝ) ≤ wfun (y + z) := wc_470 (y + z) (by linarith) (by linarith)
                have hw5 : (1618505281/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1081 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
                have hw4 : (17536657/2000000000000:ℝ) ≤ wfun (y + z) := wc_474 (y + z) (by linarith) (by linarith)
                have hw5 : (816928633/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1089 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32491/16384:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
                have hw4 : (8277259/1000000000000:ℝ) ≤ wfun (y + z) := wc_470 (y + z) (by linarith) (by linarith)
                have hw5 : (816928633/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1089 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (82806113/10000000000000:ℝ) ≤ wfun (x + y) := wc_469 (x + y) (by linarith) (by linarith)
                have hw4 : (17536657/2000000000000:ℝ) ≤ wfun (y + z) := wc_474 (y + z) (by linarith) (by linarith)
                have hw5 : (1649276337/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1091 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (14674493/2000000000000:ℝ) ≤ wfun (x + y) := wc_462 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (824390719/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1092 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (39001141/5000000000000:ℝ) ≤ wfun (x + y) := wc_468 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (1664262897/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1097 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total x (8579/8192:ℝ) with hc | hc
      · rcases le_total y (16243/8192:ℝ) with hc | hc
        · rcases le_total z (8599/8192:ℝ) with hc | hc
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (56260189/10000000000000:ℝ) ≤ wfun (x + y) := wc_446 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (1618019543/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1082 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (30163501/5000000000000:ℝ) ≤ wfun (x + y) := wc_454 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (1633366957/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1090 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
            have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
            have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
            have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
            have hw5 : (65931469/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1093 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (8599/8192:ℝ) with hc | hc
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (64534721/10000000000000:ℝ) ≤ wfun (x + y) := wc_456 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (824390719/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1092 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (68883243/10000000000000:ℝ) ≤ wfun (x + y) := wc_460 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (1664262897/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1097 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
            have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
            have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
            have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
            have hw5 : (52478353/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1099 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total y (16243/8192:ℝ) with hc | hc
        · rcases le_total z (8599/8192:ℝ) with hc | hc
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (64534721/10000000000000:ℝ) ≤ wfun (x + y) := wc_456 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (824390719/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1092 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (68883243/10000000000000:ℝ) ≤ wfun (x + y) := wc_460 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (1664262897/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1097 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
            have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
            have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
            have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
            have hw5 : (52478353/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1099 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (8599/8192:ℝ) with hc | hc
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (14674493/2000000000000:ℝ) ≤ wfun (x + y) := wc_462 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (1679811243/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1098 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (39001141/5000000000000:ℝ) ≤ wfun (x + y) := wc_468 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (1695426389/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1111 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
            have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
            have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
            have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
            have hw5 : (342118997/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1113 (x + y + z) (by linarith) (by linarith)
            linarith

set_option maxHeartbeats 20000000 in
lemma ch_139 (x y z : ℝ) (hx1 : (4297/4096:ℝ) ≤ x) (hx2 : x ≤ (2151/2048:ℝ))
    (hy1 : (1013/512:ℝ) ≤ y) (hy2 : y ≤ (4057/2048:ℝ))
    (hz1 : (267/256:ℝ) ≤ z) (hz2 : z ≤ (2141/2048:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total y (8109/4096:ℝ) with hc | hc
  · rcases le_total z (4277/4096:ℝ) with hc | hc
    · rcases le_total x (8599/8192:ℝ) with hc | hc
      · rcases le_total y (16213/8192:ℝ) with hc | hc
        · rcases le_total z (8549/8192:ℝ) with hc | hc
          · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
            have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
            have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_433 (x + y) (by linarith) (by linarith)
            have hw4 : (1187329/10000000000000:ℝ) ≤ wfun (y + z) := wc_357 (y + z) (by linarith) (by linarith)
            have hw5 : (253929443/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_943 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
            have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
            have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_433 (x + y) (by linarith) (by linarith)
            have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
            have hw5 : (1297131539/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_953 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (8549/8192:ℝ) with hc | hc
          · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
            have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
            have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_441 (x + y) (by linarith) (by linarith)
            have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
            have hw5 : (1297131539/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_953 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
            have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
            have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_441 (x + y) (by linarith) (by linarith)
            have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
            have hw5 : (1324891991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_963 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total y (16213/8192:ℝ) with hc | hc
        · rcases le_total z (8549/8192:ℝ) with hc | hc
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
            have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_441 (x + y) (by linarith) (by linarith)
            have hw4 : (1187329/10000000000000:ℝ) ≤ wfun (y + z) := wc_357 (y + z) (by linarith) (by linarith)
            have hw5 : (1297131539/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_953 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
            have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_441 (x + y) (by linarith) (by linarith)
            have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
            have hw5 : (1324891991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_963 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (8549/8192:ℝ) with hc | hc
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
            have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
            have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
            have hw5 : (1324891991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_963 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
            have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
            have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
            have hw5 : (1352927899/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_978 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total x (8599/8192:ℝ) with hc | hc
      · rcases le_total y (16213/8192:ℝ) with hc | hc
        · rcases le_total z (8559/8192:ℝ) with hc | hc
          · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
            have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
            have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
            have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_433 (x + y) (by linarith) (by linarith)
            have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
            have hw5 : (1324891991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_963 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (17193/16384:ℝ) with hc | hc
            · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (10351009/2500000000000:ℝ) ≤ wfun (x + y) := wc_432 (x + y) (by linarith) (by linarith)
              have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
              have hw5 : (84583411/625000000000:ℝ) ≤ wfun (x + y + z) := wc_977 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_80 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (22453103/5000000000000:ℝ) ≤ wfun (x + y) := wc_438 (x + y) (by linarith) (by linarith)
              have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
              have hw5 : (1367459827/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_983 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (8559/8192:ℝ) with hc | hc
          · rcases le_total x (17193/16384:ℝ) with hc | hc
            · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (48549689/10000000000000:ℝ) ≤ wfun (x + y) := wc_440 (x + y) (by linarith) (by linarith)
              have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
              have hw5 : (84583411/625000000000:ℝ) ≤ wfun (x + y + z) := wc_977 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_80 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (3270899/625000000000:ℝ) ≤ wfun (x + y) := wc_444 (x + y) (by linarith) (by linarith)
              have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
              have hw5 : (1367459827/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_983 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17193/16384:ℝ) with hc | hc
            · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (48549689/10000000000000:ℝ) ≤ wfun (x + y) := wc_440 (x + y) (by linarith) (by linarith)
              have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
              have hw5 : (1381653711/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_986 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_80 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (3270899/625000000000:ℝ) ≤ wfun (x + y) := wc_444 (x + y) (by linarith) (by linarith)
              have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
              have hw5 : (1395916139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_995 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total y (16213/8192:ℝ) with hc | hc
        · rcases le_total z (8559/8192:ℝ) with hc | hc
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
            have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
            have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_441 (x + y) (by linarith) (by linarith)
            have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
            have hw5 : (1352927899/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_978 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_441 (x + y) (by linarith) (by linarith)
            have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
            have hw5 : (690619293/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_987 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (8559/8192:ℝ) with hc | hc
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
            have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
            have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
            have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
            have hw5 : (690619293/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_987 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (17203/16384:ℝ) with hc | hc
            · have hw0 : (207931583/5000000000000:ℝ) ≤ wfun x := wc_81 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (56260189/10000000000000:ℝ) ≤ wfun (x + y) := wc_446 (x + y) (by linarith) (by linarith)
              have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
              have hw5 : (1410247029/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_998 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_83 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (30163501/5000000000000:ℝ) ≤ wfun (x + y) := wc_454 (x + y) (by linarith) (by linarith)
              have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
              have hw5 : (356161573/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1004 (x + y + z) (by linarith) (by linarith)
              linarith
  · rcases le_total z (4277/4096:ℝ) with hc | hc
    · rcases le_total x (8599/8192:ℝ) with hc | hc
      · rcases le_total y (16223/8192:ℝ) with hc | hc
        · rcases le_total z (8549/8192:ℝ) with hc | hc
          · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
            have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
            have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
            have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
            have hw5 : (1324891991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_963 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
            have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
            have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
            have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
            have hw5 : (1352927899/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_978 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (8549/8192:ℝ) with hc | hc
          · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
            have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
            have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
            have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
            have hw5 : (1352927899/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_978 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
            have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
            have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
            have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
            have hw5 : (690619293/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_987 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total y (16223/8192:ℝ) with hc | hc
        · rcases le_total z (8549/8192:ℝ) with hc | hc
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
            have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
            have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
            have hw5 : (1352927899/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_978 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
            have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
            have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
            have hw5 : (690619293/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_987 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (8549/8192:ℝ) with hc | hc
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
            have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
            have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
            have hw5 : (690619293/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_987 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
            have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
            have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
            have hw5 : (1409823377/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_999 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total x (8599/8192:ℝ) with hc | hc
      · rcases le_total y (16223/8192:ℝ) with hc | hc
        · rcases le_total z (8559/8192:ℝ) with hc | hc
          · rcases le_total x (17193/16384:ℝ) with hc | hc
            · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (56260189/10000000000000:ℝ) ≤ wfun (x + y) := wc_446 (x + y) (by linarith) (by linarith)
              have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
              have hw5 : (1381653711/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_986 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_80 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (30163501/5000000000000:ℝ) ≤ wfun (x + y) := wc_454 (x + y) (by linarith) (by linarith)
              have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
              have hw5 : (1395916139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_995 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17193/16384:ℝ) with hc | hc
            · rcases le_total y (32441/16384:ℝ) with hc | hc
              · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
                have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
                have hw4 : (7088219/5000000000000:ℝ) ≤ wfun (y + z) := wc_394 (y + z) (by linarith) (by linarith)
                have hw5 : (1410670839/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_997 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
                have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (650401/400000000000:ℝ) ≤ wfun (y + z) := wc_398 (y + z) (by linarith) (by linarith)
                have hw5 : (712537199/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1003 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_80 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (30163501/5000000000000:ℝ) ≤ wfun (x + y) := wc_454 (x + y) (by linarith) (by linarith)
              have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
              have hw5 : (356161573/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1004 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (8559/8192:ℝ) with hc | hc
          · rcases le_total x (17193/16384:ℝ) with hc | hc
            · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (64534721/10000000000000:ℝ) ≤ wfun (x + y) := wc_456 (x + y) (by linarith) (by linarith)
              have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
              have hw5 : (1410247029/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_998 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_80 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (68883243/10000000000000:ℝ) ≤ wfun (x + y) := wc_460 (x + y) (by linarith) (by linarith)
              have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
              have hw5 : (356161573/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1004 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17193/16384:ℝ) with hc | hc
            · rcases le_total y (32451/16384:ℝ) with hc | hc
              · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
                have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
                have hw5 : (719773133/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1006 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
                have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                have hw4 : (10426997/5000000000000:ℝ) ≤ wfun (y + z) := wc_406 (y + z) (by linarith) (by linarith)
                have hw5 : (1454086357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1027 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_80 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (68883243/10000000000000:ℝ) ≤ wfun (x + y) := wc_460 (x + y) (by linarith) (by linarith)
              have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
              have hw5 : (726824801/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1028 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total y (16223/8192:ℝ) with hc | hc
        · rcases le_total z (8559/8192:ℝ) with hc | hc
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
            have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
            have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
            have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
            have hw5 : (1409823377/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_999 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (17203/16384:ℝ) with hc | hc
            · have hw0 : (207931583/5000000000000:ℝ) ≤ wfun x := wc_81 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (64534721/10000000000000:ℝ) ≤ wfun (x + y) := wc_456 (x + y) (by linarith) (by linarith)
              have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
              have hw5 : (287822769/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1007 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_83 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (68883243/10000000000000:ℝ) ≤ wfun (x + y) := wc_460 (x + y) (by linarith) (by linarith)
              have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
              have hw5 : (726824801/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1028 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (8559/8192:ℝ) with hc | hc
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
            have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
            have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
            have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
            have hw5 : (1438681587/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1008 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (17203/16384:ℝ) with hc | hc
            · have hw0 : (207931583/5000000000000:ℝ) ≤ wfun x := wc_81 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (14674493/2000000000000:ℝ) ≤ wfun (x + y) := wc_462 (x + y) (by linarith) (by linarith)
              have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
              have hw5 : (58730139/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1031 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_83 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (39001141/5000000000000:ℝ) ≤ wfun (x + y) := wc_468 (x + y) (by linarith) (by linarith)
              have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
              have hw5 : (1482925379/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1037 (x + y + z) (by linarith) (by linarith)
              linarith

set_option maxHeartbeats 20000000 in
lemma ch_156 (x y z : ℝ) (hx1 : (1073/1024:ℝ) ≤ x) (hx2 : x ≤ (2151/2048:ℝ))
    (hy1 : (2031/1024:ℝ) ≤ y) (hy2 : y ≤ (4067/2048:ℝ))
    (hz1 : (267/256:ℝ) ≤ z) (hz2 : z ≤ (2141/2048:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (4297/4096:ℝ) with hc | hc
  · rcases le_total y (8129/4096:ℝ) with hc | hc
    · rcases le_total z (4277/4096:ℝ) with hc | hc
      · rcases le_total x (8589/8192:ℝ) with hc | hc
        · rcases le_total y (16253/8192:ℝ) with hc | hc
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
              have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
              have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
              have hw5 : (1438681587/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1008 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (17173/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                have hw3 : (92734261/10000000000000:ℝ) ≤ wfun (x + y) := wc_476 (x + y) (by linarith) (by linarith)
                have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
                have hw5 : (58730139/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1031 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                have hw3 : (97925413/10000000000000:ℝ) ≤ wfun (x + y) := wc_495 (x + y) (by linarith) (by linarith)
                have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
                have hw5 : (1482925379/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1037 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
              have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
              have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
              have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (17173/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                have hw3 : (20651327/2000000000000:ℝ) ≤ wfun (x + y) := wc_497 (x + y) (by linarith) (by linarith)
                have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
                have hw5 : (1497665227/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1040 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                have hw3 : (108727819/10000000000000:ℝ) ≤ wfun (x + y) := wc_501 (x + y) (by linarith) (by linarith)
                have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
                have hw5 : (1512472933/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1049 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total y (16253/8192:ℝ) with hc | hc
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
              have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
              have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (17183/16384:ℝ) with hc | hc
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                have hw3 : (20651327/2000000000000:ℝ) ≤ wfun (x + y) := wc_497 (x + y) (by linarith) (by linarith)
                have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
                have hw5 : (1497665227/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1040 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
                have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                have hw3 : (108727819/10000000000000:ℝ) ≤ wfun (x + y) := wc_501 (x + y) (by linarith) (by linarith)
                have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
                have hw5 : (1512472933/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1049 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
              have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
              have hw5 : (748607759/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1041 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
              have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
              have hw5 : (11928827/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1053 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (8589/8192:ℝ) with hc | hc
        · rcases le_total y (16253/8192:ℝ) with hc | hc
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · rcases le_total x (17173/16384:ℝ) with hc | hc
              · rcases le_total y (32501/16384:ℝ) with hc | hc
                · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                  have hw1 : (3962835597/10000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
                  have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                  have hw3 : (92771811/10000000000000:ℝ) ≤ wfun (x + y) := wc_475 (x + y) (by linarith) (by linarith)
                  have hw4 : (10351009/2500000000000:ℝ) ≤ wfun (y + z) := wc_432 (y + z) (by linarith) (by linarith)
                  have hw5 : (749057553/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1039 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                  have hw1 : (488744817/1250000000000:ℝ) ≤ wfun y := wc_197 y (by linarith) (by linarith)
                  have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                  have hw3 : (97965061/10000000000000:ℝ) ≤ wfun (x + y) := wc_494 (x + y) (by linarith) (by linarith)
                  have hw4 : (22453103/5000000000000:ℝ) ≤ wfun (y + z) := wc_438 (y + z) (by linarith) (by linarith)
                  have hw5 : (60517089/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1048 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (97925413/10000000000000:ℝ) ≤ wfun (x + y) := wc_495 (x + y) (by linarith) (by linarith)
                have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
                have hw5 : (1512472933/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1049 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (17173/16384:ℝ) with hc | hc
              · rcases le_total y (32501/16384:ℝ) with hc | hc
                · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                  have hw1 : (3962835597/10000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                  have hw3 : (92771811/10000000000000:ℝ) ≤ wfun (x + y) := wc_475 (x + y) (by linarith) (by linarith)
                  have hw4 : (48549689/10000000000000:ℝ) ≤ wfun (y + z) := wc_440 (y + z) (by linarith) (by linarith)
                  have hw5 : (305561427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1051 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                  have hw1 : (488744817/1250000000000:ℝ) ≤ wfun y := wc_197 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                  have hw3 : (97965061/10000000000000:ℝ) ≤ wfun (x + y) := wc_494 (x + y) (by linarith) (by linarith)
                  have hw4 : (3270899/625000000000:ℝ) ≤ wfun (y + z) := wc_444 (y + z) (by linarith) (by linarith)
                  have hw5 : (1542754747/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1057 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (32501/16384:ℝ) with hc | hc
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                  have hw1 : (3962835597/10000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                  have hw3 : (97965061/10000000000000:ℝ) ≤ wfun (x + y) := wc_494 (x + y) (by linarith) (by linarith)
                  have hw4 : (48549689/10000000000000:ℝ) ≤ wfun (y + z) := wc_440 (y + z) (by linarith) (by linarith)
                  have hw5 : (1542754747/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1057 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                  have hw1 : (488744817/1250000000000:ℝ) ≤ wfun y := wc_197 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                  have hw3 : (103298437/10000000000000:ℝ) ≤ wfun (x + y) := wc_496 (x + y) (by linarith) (by linarith)
                  have hw4 : (3270899/625000000000:ℝ) ≤ wfun (y + z) := wc_444 (y + z) (by linarith) (by linarith)
                  have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
                  linarith
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · rcases le_total x (17173/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (20651327/2000000000000:ℝ) ≤ wfun (x + y) := wc_497 (x + y) (by linarith) (by linarith)
                have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
                have hw5 : (1527348409/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1052 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (108727819/10000000000000:ℝ) ≤ wfun (x + y) := wc_501 (x + y) (by linarith) (by linarith)
                have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
                have hw5 : (96393223/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1058 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (17173/16384:ℝ) with hc | hc
              · rcases le_total y (32511/16384:ℝ) with hc | hc
                · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                  have hw1 : (3857446169/10000000000000:ℝ) ≤ wfun y := wc_198 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                  have hw3 : (103298437/10000000000000:ℝ) ≤ wfun (x + y) := wc_496 (x + y) (by linarith) (by linarith)
                  have hw4 : (56260189/10000000000000:ℝ) ≤ wfun (y + z) := wc_446 (y + z) (by linarith) (by linarith)
                  have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                  have hw1 : (951324587/2500000000000:ℝ) ≤ wfun y := wc_200 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                  have hw3 : (108771831/10000000000000:ℝ) ≤ wfun (x + y) := wc_500 (x + y) (by linarith) (by linarith)
                  have hw4 : (30163501/5000000000000:ℝ) ≤ wfun (y + z) := wc_454 (y + z) (by linarith) (by linarith)
                  have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (108727819/10000000000000:ℝ) ≤ wfun (x + y) := wc_501 (x + y) (by linarith) (by linarith)
                have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
                have hw5 : (314476117/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1073 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total y (16253/8192:ℝ) with hc | hc
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · rcases le_total x (17183/16384:ℝ) with hc | hc
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (20651327/2000000000000:ℝ) ≤ wfun (x + y) := wc_497 (x + y) (by linarith) (by linarith)
                have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
                have hw5 : (1527348409/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1052 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
                have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (108727819/10000000000000:ℝ) ≤ wfun (x + y) := wc_501 (x + y) (by linarith) (by linarith)
                have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
                have hw5 : (96393223/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1058 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (17183/16384:ℝ) with hc | hc
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (20651327/2000000000000:ℝ) ≤ wfun (x + y) := wc_497 (x + y) (by linarith) (by linarith)
                have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
                have hw5 : (778651161/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1061 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
                have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (108727819/10000000000000:ℝ) ≤ wfun (x + y) := wc_501 (x + y) (by linarith) (by linarith)
                have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
                have hw5 : (314476117/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1073 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · rcases le_total x (17183/16384:ℝ) with hc | hc
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (57169429/5000000000000:ℝ) ≤ wfun (x + y) := wc_503 (x + y) (by linarith) (by linarith)
                have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
                have hw5 : (778651161/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1061 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
                have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (60044823/5000000000000:ℝ) ≤ wfun (x + y) := wc_508 (x + y) (by linarith) (by linarith)
                have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
                have hw5 : (314476117/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1073 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (17183/16384:ℝ) with hc | hc
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (57169429/5000000000000:ℝ) ≤ wfun (x + y) := wc_503 (x + y) (by linarith) (by linarith)
                have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
                have hw5 : (396881567/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1075 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
                have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (60044823/5000000000000:ℝ) ≤ wfun (x + y) := wc_508 (x + y) (by linarith) (by linarith)
                have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
                have hw5 : (1602739283/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1080 (x + y + z) (by linarith) (by linarith)
                linarith
    · rcases le_total z (4277/4096:ℝ) with hc | hc
      · rcases le_total x (8589/8192:ℝ) with hc | hc
        · rcases le_total y (16263/8192:ℝ) with hc | hc
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
              have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
              have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
              have hw5 : (748607759/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1041 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
              have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
              have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
              have hw5 : (11928827/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1053 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
              have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
              have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
              have hw5 : (11928827/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1053 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
              have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
              have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
              have hw5 : (778417423/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1062 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16263/8192:ℝ) with hc | hc
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
              have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
              have hw5 : (11928827/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1053 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
              have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
              have hw5 : (778417423/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1062 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
              have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
              have hw5 : (778417423/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1062 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
              have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
              have hw5 : (1587049791/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1076 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (8589/8192:ℝ) with hc | hc
        · rcases le_total y (16263/8192:ℝ) with hc | hc
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · rcases le_total x (17173/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (57169429/5000000000000:ℝ) ≤ wfun (x + y) := wc_503 (x + y) (by linarith) (by linarith)
                have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
                have hw5 : (778651161/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1061 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (60044823/5000000000000:ℝ) ≤ wfun (x + y) := wc_508 (x + y) (by linarith) (by linarith)
                have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
                have hw5 : (314476117/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1073 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (17173/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (57169429/5000000000000:ℝ) ≤ wfun (x + y) := wc_503 (x + y) (by linarith) (by linarith)
                have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
                have hw5 : (396881567/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1075 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (60044823/5000000000000:ℝ) ≤ wfun (x + y) := wc_508 (x + y) (by linarith) (by linarith)
                have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
                have hw5 : (1602739283/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1080 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
              have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
              have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
              have hw5 : (1587049791/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1076 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (17173/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (62990037/5000000000000:ℝ) ≤ wfun (x + y) := wc_509 (x + y) (by linarith) (by linarith)
                have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
                have hw5 : (1618019543/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1082 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (66005017/5000000000000:ℝ) ≤ wfun (x + y) := wc_512 (x + y) (by linarith) (by linarith)
                have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
                have hw5 : (1633366957/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1090 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total y (16263/8192:ℝ) with hc | hc
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
              have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
              have hw5 : (1587049791/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1076 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (17183/16384:ℝ) with hc | hc
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (62990037/5000000000000:ℝ) ≤ wfun (x + y) := wc_509 (x + y) (by linarith) (by linarith)
                have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
                have hw5 : (1618019543/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1082 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
                have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (66005017/5000000000000:ℝ) ≤ wfun (x + y) := wc_512 (x + y) (by linarith) (by linarith)
                have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
                have hw5 : (1633366957/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1090 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
              have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
              have hw5 : (1617533987/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1083 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
              have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
              have hw5 : (65931469/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1093 (x + y + z) (by linarith) (by linarith)
              linarith
  · rcases le_total y (8129/4096:ℝ) with hc | hc
    · rcases le_total z (4277/4096:ℝ) with hc | hc
      · rcases le_total x (8599/8192:ℝ) with hc | hc
        · rcases le_total y (16253/8192:ℝ) with hc | hc
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
              have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
              have hw5 : (748607759/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1041 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
              have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
              have hw5 : (11928827/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1053 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
              have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
              have hw5 : (11928827/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1053 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
              have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
              have hw5 : (778417423/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1062 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16253/8192:ℝ) with hc | hc
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
              have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
              have hw5 : (11928827/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1053 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
              have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
              have hw5 : (778417423/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1062 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
              have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
              have hw5 : (778417423/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1062 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
              have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
              have hw5 : (1587049791/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1076 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (8599/8192:ℝ) with hc | hc
        · rcases le_total y (16253/8192:ℝ) with hc | hc
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
              have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
              have hw5 : (778417423/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1062 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (17193/16384:ℝ) with hc | hc
              · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
                have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (57169429/5000000000000:ℝ) ≤ wfun (x + y) := wc_503 (x + y) (by linarith) (by linarith)
                have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
                have hw5 : (396881567/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1075 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_80 x (by linarith) (by linarith)
                have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (60044823/5000000000000:ℝ) ≤ wfun (x + y) := wc_508 (x + y) (by linarith) (by linarith)
                have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
                have hw5 : (1602739283/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1080 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
              have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
              have hw5 : (1587049791/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1076 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
              have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
              have hw5 : (1617533987/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1083 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16253/8192:ℝ) with hc | hc
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
              have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
              have hw5 : (1587049791/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1076 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
              have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
              have hw5 : (1617533987/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1083 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
              have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
              have hw5 : (1617533987/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1083 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
              have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
              have hw5 : (65931469/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1093 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total z (4277/4096:ℝ) with hc | hc
      · rcases le_total x (8599/8192:ℝ) with hc | hc
        · rcases le_total y (16263/8192:ℝ) with hc | hc
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
              have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
              have hw5 : (778417423/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1062 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
              have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
              have hw5 : (1587049791/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1076 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
              have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
              have hw5 : (1587049791/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1076 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
              have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
              have hw5 : (1617533987/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1083 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16263/8192:ℝ) with hc | hc
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
            have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
            have hw4 : (4135373/1000000000000:ℝ) ≤ wfun (y + z) := wc_434 (y + z) (by linarith) (by linarith)
            have hw5 : (793048687/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1077 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
            have hw3 : (16418259/1000000000000:ℝ) ≤ wfun (x + y) := wc_521 (x + y) (by linarith) (by linarith)
            have hw4 : (48490713/10000000000000:ℝ) ≤ wfun (y + z) := wc_442 (y + z) (by linarith) (by linarith)
            have hw5 : (1616563421/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1084 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total x (8599/8192:ℝ) with hc | hc
        · rcases le_total y (16263/8192:ℝ) with hc | hc
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
              have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
              have hw5 : (1617533987/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1083 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
              have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
              have hw5 : (65931469/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1093 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
              have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
              have hw5 : (65931469/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1093 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
              have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
              have hw5 : (52478353/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1099 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16263/8192:ℝ) with hc | hc
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
              have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
              have hw5 : (65931469/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1093 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
              have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
              have hw5 : (52478353/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1099 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (16418259/1000000000000:ℝ) ≤ wfun (x + y) := wc_521 (x + y) (by linarith) (by linarith)
              have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
              have hw5 : (52478353/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1099 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (16418259/1000000000000:ℝ) ≤ wfun (x + y) := wc_521 (x + y) (by linarith) (by linarith)
              have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
              have hw5 : (342118997/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1113 (x + y + z) (by linarith) (by linarith)
              linarith

set_option maxHeartbeats 20000000 in
lemma ch_163 (x y z : ℝ) (hx1 : (539/512:ℝ) ≤ x) (hx2 : x ≤ (17/16:ℝ))
    (hy1 : (63/32:ℝ) ≤ y) (hy2 : y ≤ (1013/512:ℝ))
    (hz1 : (539/512:ℝ) ≤ z) (hz2 : z ≤ (17/16:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (1083/1024:ℝ) with hc | hc
  · rcases le_total y (2021/1024:ℝ) with hc | hc
    · rcases le_total z (1083/1024:ℝ) with hc | hc
      · rcases le_total x (2161/2048:ℝ) with hc | hc
        · rcases le_total y (4037/2048:ℝ) with hc | hc
          · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_93 x (by linarith) (by linarith)
            have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_130 y (by linarith) (by linarith)
            have hw3 : (1181561/10000000000000:ℝ) ≤ wfun (x + y) := wc_361 (x + y) (by linarith) (by linarith)
            have hw4 : (235547/2000000000000:ℝ) ≤ wfun (y + z) := wc_362 (y + z) (by linarith) (by linarith)
            have hw5 : (1427499659/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1015 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_93 x (by linarith) (by linarith)
            have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_137 y (by linarith) (by linarith)
            have hw3 : (2076333/2000000000000:ℝ) ≤ wfun (x + y) := wc_389 (x + y) (by linarith) (by linarith)
            have hw4 : (5174037/5000000000000:ℝ) ≤ wfun (y + z) := wc_390 (y + z) (by linarith) (by linarith)
            have hw5 : (1544741841/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1069 (x + y + z) (by linarith) (by linarith)
            linarith
        · have hw1 : (2946158453/5000000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
          have hw3 : (5174037/5000000000000:ℝ) ≤ wfun (x + y) := wc_390 (x + y) (by linarith) (by linarith)
          have hw4 : (293481/2500000000000:ℝ) ≤ wfun (y + z) := wc_363 (y + z) (by linarith) (by linarith)
          have hw5 : (1541044571/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1070 (x + y + z) (by linarith) (by linarith)
          linarith
      · have hw1 : (2946158453/5000000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
        have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_98 z (by linarith) (by linarith)
        have hw3 : (293481/2500000000000:ℝ) ≤ wfun (x + y) := wc_363 (x + y) (by linarith) (by linarith)
        have hw4 : (28474189/10000000000000:ℝ) ≤ wfun (y + z) := wc_421 (y + z) (by linarith) (by linarith)
        have hw5 : (1658311191/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1108 (x + y + z) (by linarith) (by linarith)
        linarith
    · rcases le_total z (1083/1024:ℝ) with hc | hc
      · rcases le_total x (2161/2048:ℝ) with hc | hc
        · rcases le_total y (4047/2048:ℝ) with hc | hc
          · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_93 x (by linarith) (by linarith)
            have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
            have hw3 : (14329561/5000000000000:ℝ) ≤ wfun (x + y) := wc_419 (x + y) (by linarith) (by linarith)
            have hw4 : (7141617/2500000000000:ℝ) ≤ wfun (y + z) := wc_420 (y + z) (by linarith) (by linarith)
            have hw5 : (1666270777/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1106 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_93 x (by linarith) (by linarith)
            have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_151 y (by linarith) (by linarith)
            have hw3 : (55964847/10000000000000:ℝ) ≤ wfun (x + y) := wc_451 (x + y) (by linarith) (by linarith)
            have hw4 : (27892031/5000000000000:ℝ) ≤ wfun (y + z) := wc_452 (y + z) (by linarith) (by linarith)
            have hw5 : (1792041507/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1134 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (4047/2048:ℝ) with hc | hc
          · have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
            have hw3 : (55964847/10000000000000:ℝ) ≤ wfun (x + y) := wc_451 (x + y) (by linarith) (by linarith)
            have hw4 : (7141617/2500000000000:ℝ) ≤ wfun (y + z) := wc_420 (y + z) (by linarith) (by linarith)
            have hw5 : (1792041507/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1134 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_151 y (by linarith) (by linarith)
            have hw3 : (92247841/10000000000000:ℝ) ≤ wfun (x + y) := wc_481 (x + y) (by linarith) (by linarith)
            have hw4 : (27892031/5000000000000:ℝ) ≤ wfun (y + z) := wc_452 (y + z) (by linarith) (by linarith)
            have hw5 : (1922008203/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1149 (x + y + z) (by linarith) (by linarith)
            linarith
      · have hw1 : (4902043129/10000000000000:ℝ) ≤ wfun y := wc_144 y (by linarith) (by linarith)
        have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_98 z (by linarith) (by linarith)
        have hw3 : (28474189/10000000000000:ℝ) ≤ wfun (x + y) := wc_421 (x + y) (by linarith) (by linarith)
        have hw4 : (11456693/1250000000000:ℝ) ≤ wfun (y + z) := wc_483 (y + z) (by linarith) (by linarith)
        have hw5 : (1912837973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1151 (x + y + z) (by linarith) (by linarith)
        linarith
  · rcases le_total y (2021/1024:ℝ) with hc | hc
    · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_98 x (by linarith) (by linarith)
      have hw1 : (2946158453/5000000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
      have hw3 : (28474189/10000000000000:ℝ) ≤ wfun (x + y) := wc_421 (x + y) (by linarith) (by linarith)
      have hw4 : (1166349/10000000000000:ℝ) ≤ wfun (y + z) := wc_364 (y + z) (by linarith) (by linarith)
      have hw5 : (12893743/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1109 (x + y + z) (by linarith) (by linarith)
      linarith
    · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_98 x (by linarith) (by linarith)
      have hw1 : (4902043129/10000000000000:ℝ) ≤ wfun y := wc_144 y (by linarith) (by linarith)
      have hw3 : (11456693/1250000000000:ℝ) ≤ wfun (x + y) := wc_483 (x + y) (by linarith) (by linarith)
      have hw4 : (28290747/10000000000000:ℝ) ≤ wfun (y + z) := wc_422 (y + z) (by linarith) (by linarith)
      have hw5 : (951861201/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1152 (x + y + z) (by linarith) (by linarith)
      linarith

set_option maxHeartbeats 20000000 in
lemma ch_175 (x y z : ℝ) (hx1 : (267/256:ℝ) ≤ x) (hx2 : x ≤ (1073/1024:ℝ))
    (hy1 : (2041/1024:ℝ) ≤ y) (hy2 : y ≤ (1023/512:ℝ))
    (hz1 : (267/256:ℝ) ≤ z) (hz2 : z ≤ (539/512:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total z (1073/1024:ℝ) with hc | hc
  · rcases le_total x (2141/2048:ℝ) with hc | hc
    · rcases le_total y (4087/2048:ℝ) with hc | hc
      · rcases le_total z (2141/2048:ℝ) with hc | hc
        · rcases le_total x (4277/4096:ℝ) with hc | hc
          · rcases le_total y (8169/4096:ℝ) with hc | hc
            · rcases le_total z (4277/4096:ℝ) with hc | hc
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                have hw1 : (2327527631/10000000000000:ℝ) ≤ wfun y := wc_228 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                have hw3 : (192151891/10000000000000:ℝ) ≤ wfun (x + y) := wc_529 (x + y) (by linarith) (by linarith)
                have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_529 (y + z) (by linarith) (by linarith)
                have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1102 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                have hw1 : (2327527631/10000000000000:ℝ) ≤ wfun y := wc_228 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (192151891/10000000000000:ℝ) ≤ wfun (x + y) := wc_529 (x + y) (by linarith) (by linarith)
                have hw4 : (890387/40000000000:ℝ) ≤ wfun (y + z) := wc_539 (y + z) (by linarith) (by linarith)
                have hw5 : (1739017297/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1121 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
              have hw1 : (2168970253/10000000000000:ℝ) ≤ wfun y := wc_231 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
              have hw3 : (890387/40000000000:ℝ) ≤ wfun (x + y) := wc_539 (x + y) (by linarith) (by linarith)
              have hw4 : (111118793/5000000000000:ℝ) ≤ wfun (y + z) := wc_540 (y + z) (by linarith) (by linarith)
              have hw5 : (434233339/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1122 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (8169/4096:ℝ) with hc | hc
            · rcases le_total z (4277/4096:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                have hw1 : (2327527631/10000000000000:ℝ) ≤ wfun y := wc_228 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                have hw3 : (890387/40000000000:ℝ) ≤ wfun (x + y) := wc_539 (x + y) (by linarith) (by linarith)
                have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_529 (y + z) (by linarith) (by linarith)
                have hw5 : (1739017297/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1121 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                have hw1 : (2327527631/10000000000000:ℝ) ≤ wfun y := wc_228 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (890387/40000000000:ℝ) ≤ wfun (x + y) := wc_539 (x + y) (by linarith) (by linarith)
                have hw4 : (890387/40000000000:ℝ) ≤ wfun (y + z) := wc_539 (y + z) (by linarith) (by linarith)
                have hw5 : (112675493/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1130 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
              have hw1 : (2168970253/10000000000000:ℝ) ≤ wfun y := wc_231 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
              have hw3 : (255244651/10000000000000:ℝ) ≤ wfun (x + y) := wc_542 (x + y) (by linarith) (by linarith)
              have hw4 : (111118793/5000000000000:ℝ) ≤ wfun (y + z) := wc_540 (y + z) (by linarith) (by linarith)
              have hw5 : (1800648153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1131 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (4277/4096:ℝ) with hc | hc
          · rcases le_total y (8169/4096:ℝ) with hc | hc
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                have hw1 : (2327527631/10000000000000:ℝ) ≤ wfun y := wc_228 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                have hw3 : (192151891/10000000000000:ℝ) ≤ wfun (x + y) := wc_529 (x + y) (by linarith) (by linarith)
                have hw4 : (255244651/10000000000000:ℝ) ≤ wfun (y + z) := wc_542 (y + z) (by linarith) (by linarith)
                have hw5 : (112675493/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1130 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                have hw1 : (2327527631/10000000000000:ℝ) ≤ wfun y := wc_228 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                have hw3 : (192151891/10000000000000:ℝ) ≤ wfun (x + y) := wc_529 (x + y) (by linarith) (by linarith)
                have hw4 : (290088193/10000000000000:ℝ) ≤ wfun (y + z) := wc_548 (y + z) (by linarith) (by linarith)
                have hw5 : (933826779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1140 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
              have hw1 : (2168970253/10000000000000:ℝ) ≤ wfun y := wc_231 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
              have hw3 : (890387/40000000000:ℝ) ≤ wfun (x + y) := wc_539 (x + y) (by linarith) (by linarith)
              have hw4 : (289620509/10000000000000:ℝ) ≤ wfun (y + z) := wc_549 (y + z) (by linarith) (by linarith)
              have hw5 : (1865416811/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1141 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (8169/4096:ℝ) with hc | hc
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                have hw1 : (2327527631/10000000000000:ℝ) ≤ wfun y := wc_228 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                have hw3 : (890387/40000000000:ℝ) ≤ wfun (x + y) := wc_539 (x + y) (by linarith) (by linarith)
                have hw4 : (255244651/10000000000000:ℝ) ≤ wfun (y + z) := wc_542 (y + z) (by linarith) (by linarith)
                have hw5 : (933826779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1140 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                have hw1 : (2327527631/10000000000000:ℝ) ≤ wfun y := wc_228 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                have hw3 : (890387/40000000000:ℝ) ≤ wfun (x + y) := wc_539 (x + y) (by linarith) (by linarith)
                have hw4 : (290088193/10000000000000:ℝ) ≤ wfun (y + z) := wc_548 (y + z) (by linarith) (by linarith)
                have hw5 : (386709691/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1145 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
              have hw1 : (2168970253/10000000000000:ℝ) ≤ wfun y := wc_231 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
              have hw3 : (255244651/10000000000000:ℝ) ≤ wfun (x + y) := wc_542 (x + y) (by linarith) (by linarith)
              have hw4 : (289620509/10000000000000:ℝ) ≤ wfun (y + z) := wc_549 (y + z) (by linarith) (by linarith)
              have hw5 : (965616743/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1146 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (2141/2048:ℝ) with hc | hc
        · rcases le_total x (4277/4096:ℝ) with hc | hc
          · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
            have hw1 : (1868712167/10000000000000:ℝ) ≤ wfun y := wc_232 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
            have hw3 : (10193319/400000000000:ℝ) ≤ wfun (x + y) := wc_543 (x + y) (by linarith) (by linarith)
            have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_544 (y + z) (by linarith) (by linarith)
            have hw5 : (1798491653/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1132 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
            have hw1 : (1868712167/10000000000000:ℝ) ≤ wfun y := wc_232 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
            have hw3 : (289620509/10000000000000:ℝ) ≤ wfun (x + y) := wc_549 (x + y) (by linarith) (by linarith)
            have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_544 (y + z) (by linarith) (by linarith)
            have hw5 : (1863183413/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1142 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total x (4277/4096:ℝ) with hc | hc
          · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
            have hw1 : (1868712167/10000000000000:ℝ) ≤ wfun y := wc_232 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
            have hw3 : (10193319/400000000000:ℝ) ≤ wfun (x + y) := wc_543 (x + y) (by linarith) (by linarith)
            have hw4 : (326066581/10000000000000:ℝ) ≤ wfun (y + z) := wc_552 (y + z) (by linarith) (by linarith)
            have hw5 : (964460991/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1147 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
            have hw1 : (1868712167/10000000000000:ℝ) ≤ wfun y := wc_232 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
            have hw3 : (289620509/10000000000000:ℝ) ≤ wfun (x + y) := wc_549 (x + y) (by linarith) (by linarith)
            have hw4 : (326066581/10000000000000:ℝ) ≤ wfun (y + z) := wc_552 (y + z) (by linarith) (by linarith)
            have hw5 : (1995701471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1160 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total y (4087/2048:ℝ) with hc | hc
      · rcases le_total z (2141/2048:ℝ) with hc | hc
        · rcases le_total x (4287/4096:ℝ) with hc | hc
          · rcases le_total y (8169/4096:ℝ) with hc | hc
            · rcases le_total z (4277/4096:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
                have hw1 : (2327527631/10000000000000:ℝ) ≤ wfun y := wc_228 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                have hw3 : (255244651/10000000000000:ℝ) ≤ wfun (x + y) := wc_542 (x + y) (by linarith) (by linarith)
                have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_529 (y + z) (by linarith) (by linarith)
                have hw5 : (112675493/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1130 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
                have hw1 : (2327527631/10000000000000:ℝ) ≤ wfun y := wc_228 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (255244651/10000000000000:ℝ) ≤ wfun (x + y) := wc_542 (x + y) (by linarith) (by linarith)
                have hw4 : (890387/40000000000:ℝ) ≤ wfun (y + z) := wc_539 (y + z) (by linarith) (by linarith)
                have hw5 : (933826779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1140 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
              have hw1 : (2168970253/10000000000000:ℝ) ≤ wfun y := wc_231 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
              have hw3 : (290088193/10000000000000:ℝ) ≤ wfun (x + y) := wc_548 (x + y) (by linarith) (by linarith)
              have hw4 : (111118793/5000000000000:ℝ) ≤ wfun (y + z) := wc_540 (y + z) (by linarith) (by linarith)
              have hw5 : (1865416811/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1141 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (8169/4096:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
              have hw1 : (2327527631/10000000000000:ℝ) ≤ wfun y := wc_228 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
              have hw3 : (290088193/10000000000000:ℝ) ≤ wfun (x + y) := wc_548 (x + y) (by linarith) (by linarith)
              have hw4 : (47960431/2500000000000:ℝ) ≤ wfun (y + z) := wc_530 (y + z) (by linarith) (by linarith)
              have hw5 : (1865416811/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1141 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
              have hw1 : (2168970253/10000000000000:ℝ) ≤ wfun y := wc_231 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
              have hw3 : (65423973/2000000000000:ℝ) ≤ wfun (x + y) := wc_550 (x + y) (by linarith) (by linarith)
              have hw4 : (111118793/5000000000000:ℝ) ≤ wfun (y + z) := wc_540 (y + z) (by linarith) (by linarith)
              have hw5 : (965616743/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1146 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (4287/4096:ℝ) with hc | hc
          · rcases le_total y (8169/4096:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
              have hw1 : (2327527631/10000000000000:ℝ) ≤ wfun y := wc_228 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
              have hw3 : (255244651/10000000000000:ℝ) ≤ wfun (x + y) := wc_542 (x + y) (by linarith) (by linarith)
              have hw4 : (10193319/400000000000:ℝ) ≤ wfun (y + z) := wc_543 (y + z) (by linarith) (by linarith)
              have hw5 : (965616743/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1146 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
              have hw1 : (2168970253/10000000000000:ℝ) ≤ wfun y := wc_231 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
              have hw3 : (290088193/10000000000000:ℝ) ≤ wfun (x + y) := wc_548 (x + y) (by linarith) (by linarith)
              have hw4 : (289620509/10000000000000:ℝ) ≤ wfun (y + z) := wc_549 (y + z) (by linarith) (by linarith)
              have hw5 : (49952307/250000000000:ℝ) ≤ wfun (x + y + z) := wc_1159 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (8169/4096:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
              have hw1 : (2327527631/10000000000000:ℝ) ≤ wfun y := wc_228 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
              have hw3 : (290088193/10000000000000:ℝ) ≤ wfun (x + y) := wc_548 (x + y) (by linarith) (by linarith)
              have hw4 : (10193319/400000000000:ℝ) ≤ wfun (y + z) := wc_543 (y + z) (by linarith) (by linarith)
              have hw5 : (49952307/250000000000:ℝ) ≤ wfun (x + y + z) := wc_1159 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
              have hw1 : (2168970253/10000000000000:ℝ) ≤ wfun y := wc_231 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
              have hw3 : (65423973/2000000000000:ℝ) ≤ wfun (x + y) := wc_550 (x + y) (by linarith) (by linarith)
              have hw4 : (289620509/10000000000000:ℝ) ≤ wfun (y + z) := wc_549 (y + z) (by linarith) (by linarith)
              have hw5 : (129124203/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1162 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (2141/2048:ℝ) with hc | hc
        · rcases le_total x (4287/4096:ℝ) with hc | hc
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
            have hw1 : (1868712167/10000000000000:ℝ) ≤ wfun y := wc_232 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
            have hw3 : (326592691/10000000000000:ℝ) ≤ wfun (x + y) := wc_551 (x + y) (by linarith) (by linarith)
            have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_544 (y + z) (by linarith) (by linarith)
            have hw5 : (964460991/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1147 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
            have hw1 : (1868712167/10000000000000:ℝ) ≤ wfun y := wc_232 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
            have hw3 : (365741913/10000000000000:ℝ) ≤ wfun (x + y) := wc_559 (x + y) (by linarith) (by linarith)
            have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_544 (y + z) (by linarith) (by linarith)
            have hw5 : (1995701471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1160 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total x (4287/4096:ℝ) with hc | hc
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
            have hw1 : (1868712167/10000000000000:ℝ) ≤ wfun y := wc_232 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
            have hw3 : (326592691/10000000000000:ℝ) ≤ wfun (x + y) := wc_551 (x + y) (by linarith) (by linarith)
            have hw4 : (326066581/10000000000000:ℝ) ≤ wfun (y + z) := wc_552 (y + z) (by linarith) (by linarith)
            have hw5 : (103175797/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1163 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
            have hw1 : (1868712167/10000000000000:ℝ) ≤ wfun y := wc_232 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
            have hw3 : (365741913/10000000000000:ℝ) ≤ wfun (x + y) := wc_559 (x + y) (by linarith) (by linarith)
            have hw4 : (326066581/10000000000000:ℝ) ≤ wfun (y + z) := wc_552 (y + z) (by linarith) (by linarith)
            have hw5 : (426471879/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1168 (x + y + z) (by linarith) (by linarith)
            linarith
  · rcases le_total x (2141/2048:ℝ) with hc | hc
    · rcases le_total y (4087/2048:ℝ) with hc | hc
      · rcases le_total z (2151/2048:ℝ) with hc | hc
        · rcases le_total x (4277/4096:ℝ) with hc | hc
          · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
            have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_229 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
            have hw3 : (47960431/2500000000000:ℝ) ≤ wfun (x + y) := wc_530 (x + y) (by linarith) (by linarith)
            have hw4 : (326066581/10000000000000:ℝ) ≤ wfun (y + z) := wc_552 (y + z) (by linarith) (by linarith)
            have hw5 : (964460991/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1147 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
            have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_229 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
            have hw3 : (111118793/5000000000000:ℝ) ≤ wfun (x + y) := wc_540 (x + y) (by linarith) (by linarith)
            have hw4 : (326066581/10000000000000:ℝ) ≤ wfun (y + z) := wc_552 (y + z) (by linarith) (by linarith)
            have hw5 : (1995701471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1160 (x + y + z) (by linarith) (by linarith)
            linarith
        · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
          have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_229 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
          have hw3 : (23941523/1250000000000:ℝ) ≤ wfun (x + y) := wc_531 (x + y) (by linarith) (by linarith)
          have hw4 : (406405247/10000000000000:ℝ) ≤ wfun (y + z) := wc_560 (y + z) (by linarith) (by linarith)
          have hw5 : (2061048329/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1164 (x + y + z) (by linarith) (by linarith)
          linarith
      · rcases le_total z (2151/2048:ℝ) with hc | hc
        · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
          have hw1 : (1868712167/10000000000000:ℝ) ≤ wfun y := wc_232 y (by linarith) (by linarith)
          have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
          have hw3 : (25442213/1000000000000:ℝ) ≤ wfun (x + y) := wc_544 (x + y) (by linarith) (by linarith)
          have hw4 : (406405247/10000000000000:ℝ) ≤ wfun (y + z) := wc_560 (y + z) (by linarith) (by linarith)
          have hw5 : (2061048329/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1164 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
          have hw1 : (1868712167/10000000000000:ℝ) ≤ wfun y := wc_232 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
          have hw3 : (25442213/1000000000000:ℝ) ≤ wfun (x + y) := wc_544 (x + y) (by linarith) (by linarith)
          have hw4 : (495376037/10000000000000:ℝ) ≤ wfun (y + z) := wc_562 (y + z) (by linarith) (by linarith)
          have hw5 : (1099796941/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1169 (x + y + z) (by linarith) (by linarith)
          linarith
    · rcases le_total y (4087/2048:ℝ) with hc | hc
      · rcases le_total z (2151/2048:ℝ) with hc | hc
        · rcases le_total x (4287/4096:ℝ) with hc | hc
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
            have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_229 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
            have hw3 : (10193319/400000000000:ℝ) ≤ wfun (x + y) := wc_543 (x + y) (by linarith) (by linarith)
            have hw4 : (326066581/10000000000000:ℝ) ≤ wfun (y + z) := wc_552 (y + z) (by linarith) (by linarith)
            have hw5 : (103175797/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1163 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
            have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_229 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
            have hw3 : (289620509/10000000000000:ℝ) ≤ wfun (x + y) := wc_549 (x + y) (by linarith) (by linarith)
            have hw4 : (326066581/10000000000000:ℝ) ≤ wfun (y + z) := wc_552 (y + z) (by linarith) (by linarith)
            have hw5 : (426471879/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1168 (x + y + z) (by linarith) (by linarith)
            linarith
        · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_56 x (by linarith) (by linarith)
          have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_229 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
          have hw3 : (25442213/1000000000000:ℝ) ≤ wfun (x + y) := wc_544 (x + y) (by linarith) (by linarith)
          have hw4 : (406405247/10000000000000:ℝ) ≤ wfun (y + z) := wc_560 (y + z) (by linarith) (by linarith)
          have hw5 : (1099796941/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1169 (x + y + z) (by linarith) (by linarith)
          linarith
      · rcases le_total z (2151/2048:ℝ) with hc | hc
        · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_56 x (by linarith) (by linarith)
          have hw1 : (1868712167/10000000000000:ℝ) ≤ wfun y := wc_232 y (by linarith) (by linarith)
          have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
          have hw3 : (326066581/10000000000000:ℝ) ≤ wfun (x + y) := wc_552 (x + y) (by linarith) (by linarith)
          have hw4 : (406405247/10000000000000:ℝ) ≤ wfun (y + z) := wc_560 (y + z) (by linarith) (by linarith)
          have hw5 : (1099796941/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1169 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_56 x (by linarith) (by linarith)
          have hw1 : (1868712167/10000000000000:ℝ) ≤ wfun y := wc_232 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
          have hw3 : (326066581/10000000000000:ℝ) ≤ wfun (x + y) := wc_552 (x + y) (by linarith) (by linarith)
          have hw4 : (495376037/10000000000000:ℝ) ≤ wfun (y + z) := wc_562 (y + z) (by linarith) (by linarith)
          have hw5 : (1171101043/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1175 (x + y + z) (by linarith) (by linarith)
          linarith

set_option maxHeartbeats 20000000 in
lemma ch_215 (x y z : ℝ) (hx1 : (63/32:ℝ) ≤ x) (hx2 : x ≤ (131/64:ℝ))
    (hy1 : (17/16:ℝ) ≤ y) (hy2 : y ≤ (73/64:ℝ))
    (hz1 : (121/64:ℝ) ≤ z) (hz2 : z ≤ (131/64:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total z (63/32:ℝ) with hc | hc
  · have hw1 : (15429929/1000000000000:ℝ) ≤ wfun y := wc_104 y (by linarith) (by linarith)
    have hw2 : (795663039/1250000000000:ℝ) ≤ wfun z := wc_117 z (by linarith) (by linarith)
    have hw3 : (75856633/10000000000000:ℝ) ≤ wfun (x + y) := wc_492 (x + y) (by linarith) (by linarith)
    linarith
  · rcases le_total x (257/128:ℝ) with hc | hc
    · rcases le_total y (141/128:ℝ) with hc | hc
      · rcases le_total z (257/128:ℝ) with hc | hc
        · rcases le_total x (509/256:ℝ) with hc | hc
          · rcases le_total y (277/256:ℝ) with hc | hc
            · rcases le_total z (509/256:ℝ) with hc | hc
              · have hw0 : (396477691/1250000000000:ℝ) ≤ wfun x := wc_133 x (by linarith) (by linarith)
                have hw1 : (38452957/2000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
                have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_133 z (by linarith) (by linarith)
                have hw3 : (88186617/10000000000000:ℝ) ≤ wfun (x + y) := wc_487 (x + y) (by linarith) (by linarith)
                have hw4 : (88186617/10000000000000:ℝ) ≤ wfun (y + z) := wc_487 (y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396477691/1250000000000:ℝ) ≤ wfun x := wc_133 x (by linarith) (by linarith)
                have hw1 : (38452957/2000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
                have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                  rcases le_total z (2:ℝ) with hq20 | hq20
                  · exact le_trans (by norm_num) (wc_220 z (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                have hw3 : (88186617/10000000000000:ℝ) ≤ wfun (x + y) := wc_487 (x + y) (by linarith) (by linarith)
                have hw4 : (66837841/1000000000000:ℝ) ≤ wfun (y + z) := wc_574 (y + z) (by linarith) (by linarith)
                have hw5 : (1405331/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_1222 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (396477691/1250000000000:ℝ) ≤ wfun x := wc_133 x (by linarith) (by linarith)
              have hw1 : (4137262453/10000000000000:ℝ) ≤ wfun y := wc_107 y (by linarith) (by linarith)
              have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                rcases le_total z (2:ℝ) with hq20 | hq20
                · exact le_trans (by norm_num) (wc_134 z (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
              have hw3 : (66837841/1000000000000:ℝ) ≤ wfun (x + y) := wc_574 (x + y) (by linarith) (by linarith)
              have hw4 : (162913869/2500000000000:ℝ) ≤ wfun (y + z) := wc_576 (y + z) (by linarith) (by linarith)
              have hw5 : (13838751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1223 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (277/256:ℝ) with hc | hc
            · rcases le_total z (509/256:ℝ) with hc | hc
              · have hw0 : (179073511/2000000000000:ℝ) ≤ wfun x := by
                  rcases le_total x (2:ℝ) with hq00 | hq00
                  · exact le_trans (by norm_num) (wc_220 x (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_236 x (by linarith) (by linarith))
                have hw1 : (38452957/2000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
                have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_133 z (by linarith) (by linarith)
                have hw3 : (66837841/1000000000000:ℝ) ≤ wfun (x + y) := wc_574 (x + y) (by linarith) (by linarith)
                have hw4 : (88186617/10000000000000:ℝ) ≤ wfun (y + z) := wc_487 (y + z) (by linarith) (by linarith)
                have hw5 : (1405331/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_1222 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total x (1023/512:ℝ) with hc | hc
                · have hw0 : (1865845891/10000000000000:ℝ) ≤ wfun x := wc_219 x (by linarith) (by linarith)
                  have hw1 : (38452957/2000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
                  have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                    rcases le_total z (2:ℝ) with hq20 | hq20
                    · exact le_trans (by norm_num) (wc_220 z (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                  have hw3 : (676941261/10000000000000:ℝ) ≤ wfun (x + y) := wc_573 (x + y) (by linarith) (by linarith)
                  have hw4 : (66837841/1000000000000:ℝ) ≤ wfun (y + z) := wc_574 (y + z) (by linarith) (by linarith)
                  have hw5 : (37716487/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1268 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (179073511/2000000000000:ℝ) ≤ wfun x := by
                    rcases le_total x (2:ℝ) with hq00 | hq00
                    · exact le_trans (by norm_num) (wc_233 x (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_236 x (by linarith) (by linarith))
                  have hw1 : (38452957/2000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
                  have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                    rcases le_total z (2:ℝ) with hq20 | hq20
                    · exact le_trans (by norm_num) (wc_220 z (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                  have hw3 : (1168886057/10000000000000:ℝ) ≤ wfun (x + y) := wc_585 (x + y) (by linarith) (by linarith)
                  have hw4 : (66837841/1000000000000:ℝ) ≤ wfun (y + z) := wc_574 (y + z) (by linarith) (by linarith)
                  have hw5 : (43578037/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1316 (x + y + z) (by linarith) (by linarith)
                  linarith
            · have hw0 : (179073511/2000000000000:ℝ) ≤ wfun x := by
                rcases le_total x (2:ℝ) with hq00 | hq00
                · exact le_trans (by norm_num) (wc_220 x (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_236 x (by linarith) (by linarith))
              have hw1 : (4137262453/10000000000000:ℝ) ≤ wfun y := wc_107 y (by linarith) (by linarith)
              have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                rcases le_total z (2:ℝ) with hq20 | hq20
                · exact le_trans (by norm_num) (wc_134 z (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
              have hw3 : (1764735511/10000000000000:ℝ) ≤ wfun (x + y) := wc_590 (x + y) (by linarith) (by linarith)
              have hw4 : (162913869/2500000000000:ℝ) ≤ wfun (y + z) := wc_576 (y + z) (by linarith) (by linarith)
              have hw5 : (5759139/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1270 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (509/256:ℝ) with hc | hc
          · have hw0 : (396477691/1250000000000:ℝ) ≤ wfun x := wc_133 x (by linarith) (by linarith)
            have hw1 : (44604923/2500000000000:ℝ) ≤ wfun y := wc_103 y (by linarith) (by linarith)
            have hw3 : (21491553/2500000000000:ℝ) ≤ wfun (x + y) := wc_488 (x + y) (by linarith) (by linarith)
            have hw4 : (419583999/2500000000000:ℝ) ≤ wfun (y + z) := wc_592 (y + z) (by linarith) (by linarith)
            have hw5 : (90750063/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1271 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (179073511/2000000000000:ℝ) ≤ wfun x := by
              rcases le_total x (2:ℝ) with hq00 | hq00
              · exact le_trans (by norm_num) (wc_220 x (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_236 x (by linarith) (by linarith))
            have hw1 : (44604923/2500000000000:ℝ) ≤ wfun y := wc_103 y (by linarith) (by linarith)
            have hw3 : (162913869/2500000000000:ℝ) ≤ wfun (x + y) := wc_576 (x + y) (by linarith) (by linarith)
            have hw4 : (419583999/2500000000000:ℝ) ≤ wfun (y + z) := wc_592 (y + z) (by linarith) (by linarith)
            have hw5 : (534939039/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1374 (x + y + z) (by linarith) (by linarith)
            linarith
      · have hw0 : (179073511/2000000000000:ℝ) ≤ wfun x := by
          rcases le_total x (2:ℝ) with hq00 | hq00
          · exact le_trans (by norm_num) (wc_134 x (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_236 x (by linarith) (by linarith))
        have hw1 : (11778340313/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
        have hw3 : (419583999/2500000000000:ℝ) ≤ wfun (x + y) := wc_592 (x + y) (by linarith) (by linarith)
        have hw4 : (798582451/5000000000000:ℝ) ≤ wfun (y + z) := wc_594 (y + z) (by linarith) (by linarith)
        have hw5 : (21679333/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1272 (x + y + z) (by linarith) (by linarith)
        linarith
    · rcases le_total y (141/128:ℝ) with hc | hc
      · rcases le_total z (257/128:ℝ) with hc | hc
        · rcases le_total x (519/256:ℝ) with hc | hc
          · rcases le_total y (277/256:ℝ) with hc | hc
            · rcases le_total z (509/256:ℝ) with hc | hc
              · have hw0 : (13164037/10000000000000:ℝ) ≤ wfun x := wc_244 x (by linarith) (by linarith)
                have hw1 : (38452957/2000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
                have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_133 z (by linarith) (by linarith)
                have hw3 : (1764735511/10000000000000:ℝ) ≤ wfun (x + y) := wc_590 (x + y) (by linarith) (by linarith)
                have hw4 : (88186617/10000000000000:ℝ) ≤ wfun (y + z) := wc_487 (y + z) (by linarith) (by linarith)
                have hw5 : (187138697/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1269 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (13164037/10000000000000:ℝ) ≤ wfun x := wc_244 x (by linarith) (by linarith)
                have hw1 : (38452957/2000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
                have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                  rcases le_total z (2:ℝ) with hq20 | hq20
                  · exact le_trans (by norm_num) (wc_220 z (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                have hw3 : (1764735511/10000000000000:ℝ) ≤ wfun (x + y) := wc_590 (x + y) (by linarith) (by linarith)
                have hw4 : (66837841/1000000000000:ℝ) ≤ wfun (y + z) := wc_574 (y + z) (by linarith) (by linarith)
                have hw5 : (551493311/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1372 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (13164037/10000000000000:ℝ) ≤ wfun x := wc_244 x (by linarith) (by linarith)
              have hw1 : (4137262453/10000000000000:ℝ) ≤ wfun y := wc_107 y (by linarith) (by linarith)
              have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                rcases le_total z (2:ℝ) with hq20 | hq20
                · exact le_trans (by norm_num) (wc_134 z (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
              have hw3 : (1670535297/5000000000000:ℝ) ≤ wfun (x + y) := wc_598 (x + y) (by linarith) (by linarith)
              have hw4 : (162913869/2500000000000:ℝ) ≤ wfun (y + z) := wc_576 (y + z) (by linarith) (by linarith)
              have hw5 : (108627463/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1373 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw1 : (44604923/2500000000000:ℝ) ≤ wfun y := wc_103 y (by linarith) (by linarith)
            have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
              rcases le_total z (2:ℝ) with hq20 | hq20
              · exact le_trans (by norm_num) (wc_134 z (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
            have hw3 : (1629257293/5000000000000:ℝ) ≤ wfun (x + y) := wc_599 (x + y) (by linarith) (by linarith)
            have hw4 : (20953831/2500000000000:ℝ) ≤ wfun (y + z) := wc_489 (y + z) (by linarith) (by linarith)
            have hw5 : (534939039/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1374 (x + y + z) (by linarith) (by linarith)
            linarith
        · have hw1 : (44604923/2500000000000:ℝ) ≤ wfun y := wc_103 y (by linarith) (by linarith)
          have hw3 : (419583999/2500000000000:ℝ) ≤ wfun (x + y) := wc_592 (x + y) (by linarith) (by linarith)
          have hw4 : (419583999/2500000000000:ℝ) ≤ wfun (y + z) := wc_592 (y + z) (by linarith) (by linarith)
          have hw5 : (1048517003/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1474 (x + y + z) (by linarith) (by linarith)
          linarith
      · have hw1 : (11778340313/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
        have hw3 : (5096134953/10000000000000:ℝ) ≤ wfun (x + y) := wc_604 (x + y) (by linarith) (by linarith)
        have hw4 : (798582451/5000000000000:ℝ) ≤ wfun (y + z) := wc_594 (y + z) (by linarith) (by linarith)
        have hw5 : (1017509707/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1475 (x + y + z) (by linarith) (by linarith)
        linarith

end Zeta23Ext.Bridge.FourPoint
