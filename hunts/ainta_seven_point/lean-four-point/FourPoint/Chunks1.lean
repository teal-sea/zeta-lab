import FourPoint.Cells

/-! Chunk module 1 of 16 of the three-dimensional table.  Each lemma is one
subtree of at most 110 leaves of one box's bisection tree; `FourPoint/Boxes.lean` routes
the box down to them.  Cutting the tree this way gives each subtree its own
heartbeat budget and lets `lake` compile them in parallel. -/

noncomputable section
namespace Zeta23Ext.Bridge.FourPoint

set_option maxHeartbeats 20000000 in
lemma ch_31 (x y z : ℝ) (hx1 : (529/512:ℝ) ≤ x) (hx2 : x ≤ (267/256:ℝ))
    (hy1 : (509/256:ℝ) ≤ y) (hy2 : y ≤ (1023/512:ℝ))
    (hz1 : (131/128:ℝ) ≤ z) (hz2 : z ≤ (267/256:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total z (529/512:ℝ) with hc | hc
  · rcases le_total x (1063/1024:ℝ) with hc | hc
    · rcases le_total y (2041/1024:ℝ) with hc | hc
      · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
        have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_218 y (by linarith) (by linarith)
        have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
        have hw3 : (293481/2500000000000:ℝ) ≤ wfun (x + y) := wc_363 (x + y) (by linarith) (by linarith)
        have hw5 : (183260287/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_803 (x + y + z) (by linarith) (by linarith)
        linarith
      · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
        have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_230 y (by linarith) (by linarith)
        have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
        have hw3 : (28474189/10000000000000:ℝ) ≤ wfun (x + y) := wc_421 (x + y) (by linarith) (by linarith)
        have hw5 : (495290917/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_814 (x + y + z) (by linarith) (by linarith)
        linarith
    · rcases le_total y (2041/1024:ℝ) with hc | hc
      · rcases le_total z (1053/1024:ℝ) with hc | hc
        · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
          have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_218 y (by linarith) (by linarith)
          have hw2 : (3436255003/5000000000000:ℝ) ≤ wfun z := wc_11 z (by linarith) (by linarith)
          have hw3 : (28474189/10000000000000:ℝ) ≤ wfun (x + y) := wc_421 (x + y) (by linarith) (by linarith)
          have hw5 : (99536523/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_813 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
          have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_218 y (by linarith) (by linarith)
          have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_15 z (by linarith) (by linarith)
          have hw3 : (28474189/10000000000000:ℝ) ≤ wfun (x + y) := wc_421 (x + y) (by linarith) (by linarith)
          have hw5 : (645862429/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_823 (x + y + z) (by linarith) (by linarith)
          linarith
      · rcases le_total z (1053/1024:ℝ) with hc | hc
        · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
          have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_230 y (by linarith) (by linarith)
          have hw2 : (3436255003/5000000000000:ℝ) ≤ wfun z := wc_11 z (by linarith) (by linarith)
          have hw3 : (11456693/1250000000000:ℝ) ≤ wfun (x + y) := wc_483 (x + y) (by linarith) (by linarith)
          have hw5 : (645862429/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_823 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
          have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_230 y (by linarith) (by linarith)
          have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_15 z (by linarith) (by linarith)
          have hw3 : (11456693/1250000000000:ℝ) ≤ wfun (x + y) := wc_483 (x + y) (by linarith) (by linarith)
          have hw4 : (293481/2500000000000:ℝ) ≤ wfun (y + z) := wc_363 (y + z) (by linarith) (by linarith)
          have hw5 : (812553443/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_850 (x + y + z) (by linarith) (by linarith)
          linarith
  · rcases le_total x (1063/1024:ℝ) with hc | hc
    · rcases le_total y (2041/1024:ℝ) with hc | hc
      · rcases le_total z (1063/1024:ℝ) with hc | hc
        · rcases le_total x (2121/2048:ℝ) with hc | hc
          · have hw0 : (1888462017/5000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
            have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_218 y (by linarith) (by linarith)
            have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
            have hw3 : (235547/2000000000000:ℝ) ≤ wfun (x + y) := wc_362 (x + y) (by linarith) (by linarith)
            have hw4 : (293481/2500000000000:ℝ) ≤ wfun (y + z) := wc_363 (y + z) (by linarith) (by linarith)
            have hw5 : (323709737/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_822 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total y (4077/2048:ℝ) with hc | hc
            · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
              have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_217 y (by linarith) (by linarith)
              have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
              have hw3 : (2076333/2000000000000:ℝ) ≤ wfun (x + y) := wc_389 (x + y) (by linarith) (by linarith)
              have hw4 : (235547/2000000000000:ℝ) ≤ wfun (y + z) := wc_362 (y + z) (by linarith) (by linarith)
              have hw5 : (730420113/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_840 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
              have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_226 y (by linarith) (by linarith)
              have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
              have hw3 : (14329561/5000000000000:ℝ) ≤ wfun (x + y) := wc_419 (x + y) (by linarith) (by linarith)
              have hw4 : (5174037/5000000000000:ℝ) ≤ wfun (y + z) := wc_390 (y + z) (by linarith) (by linarith)
              have hw5 : (25514763/312500000000:ℝ) ≤ wfun (x + y + z) := wc_848 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (2121/2048:ℝ) with hc | hc
          · rcases le_total y (4077/2048:ℝ) with hc | hc
            · have hw0 : (1888462017/5000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
              have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_217 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
              have hw3 : (1181561/10000000000000:ℝ) ≤ wfun (x + y) := wc_361 (x + y) (by linarith) (by linarith)
              have hw4 : (7141617/2500000000000:ℝ) ≤ wfun (y + z) := wc_420 (y + z) (by linarith) (by linarith)
              have hw5 : (25514763/312500000000:ℝ) ≤ wfun (x + y + z) := wc_848 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1888462017/5000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
              have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_226 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
              have hw3 : (2076333/2000000000000:ℝ) ≤ wfun (x + y) := wc_389 (x + y) (by linarith) (by linarith)
              have hw4 : (27892031/5000000000000:ℝ) ≤ wfun (y + z) := wc_452 (y + z) (by linarith) (by linarith)
              have hw5 : (907100611/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_861 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (4077/2048:ℝ) with hc | hc
            · rcases le_total z (2131/2048:ℝ) with hc | hc
              · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
                have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_217 y (by linarith) (by linarith)
                have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                have hw3 : (2076333/2000000000000:ℝ) ≤ wfun (x + y) := wc_389 (x + y) (by linarith) (by linarith)
                have hw4 : (14329561/5000000000000:ℝ) ≤ wfun (y + z) := wc_419 (y + z) (by linarith) (by linarith)
                have hw5 : (56830383/625000000000:ℝ) ≤ wfun (x + y + z) := wc_860 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total x (4247/4096:ℝ) with hc | hc
                · have hw0 : (1676998161/5000000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
                  have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_217 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                  have hw3 : (649907/625000000000:ℝ) ≤ wfun (x + y) := wc_388 (x + y) (by linarith) (by linarith)
                  have hw4 : (55964847/10000000000000:ℝ) ≤ wfun (y + z) := wc_451 (y + z) (by linarith) (by linarith)
                  have hw5 : (1005888959/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_873 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_22 x (by linarith) (by linarith)
                  have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_217 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                  have hw3 : (736743/400000000000:ℝ) ≤ wfun (x + y) := wc_404 (x + y) (by linarith) (by linarith)
                  have hw4 : (55964847/10000000000000:ℝ) ≤ wfun (y + z) := wc_451 (y + z) (by linarith) (by linarith)
                  have hw5 : (1055337947/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_889 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total z (2131/2048:ℝ) with hc | hc
              · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
                have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_226 y (by linarith) (by linarith)
                have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                have hw3 : (14329561/5000000000000:ℝ) ≤ wfun (x + y) := wc_419 (x + y) (by linarith) (by linarith)
                have hw4 : (55964847/10000000000000:ℝ) ≤ wfun (y + z) := wc_451 (y + z) (by linarith) (by linarith)
                have hw5 : (1004679561/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_874 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
                have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_226 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                have hw3 : (14329561/5000000000000:ℝ) ≤ wfun (x + y) := wc_419 (x + y) (by linarith) (by linarith)
                have hw4 : (92247841/10000000000000:ℝ) ≤ wfun (y + z) := wc_481 (y + z) (by linarith) (by linarith)
                have hw5 : (8629543/78125000000:ℝ) ≤ wfun (x + y + z) := wc_899 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total z (1063/1024:ℝ) with hc | hc
        · rcases le_total x (2121/2048:ℝ) with hc | hc
          · have hw0 : (1888462017/5000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
            have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_230 y (by linarith) (by linarith)
            have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
            have hw3 : (7141617/2500000000000:ℝ) ≤ wfun (x + y) := wc_420 (x + y) (by linarith) (by linarith)
            have hw4 : (28474189/10000000000000:ℝ) ≤ wfun (y + z) := wc_421 (y + z) (by linarith) (by linarith)
            have hw5 : (407254991/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_849 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
            have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_230 y (by linarith) (by linarith)
            have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
            have hw3 : (27892031/5000000000000:ℝ) ≤ wfun (x + y) := wc_452 (x + y) (by linarith) (by linarith)
            have hw4 : (28474189/10000000000000:ℝ) ≤ wfun (y + z) := wc_421 (y + z) (by linarith) (by linarith)
            have hw5 : (45246083/500000000000:ℝ) ≤ wfun (x + y + z) := wc_862 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total x (2121/2048:ℝ) with hc | hc
          · rcases le_total y (4087/2048:ℝ) with hc | hc
            · have hw0 : (1888462017/5000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
              have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_229 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
              have hw3 : (14329561/5000000000000:ℝ) ≤ wfun (x + y) := wc_419 (x + y) (by linarith) (by linarith)
              have hw4 : (22987523/2500000000000:ℝ) ≤ wfun (y + z) := wc_482 (y + z) (by linarith) (by linarith)
              have hw5 : (200453243/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_875 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1888462017/5000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
              have hw1 : (1868712167/10000000000000:ℝ) ≤ wfun y := wc_232 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
              have hw3 : (55964847/10000000000000:ℝ) ≤ wfun (x + y) := wc_451 (x + y) (by linarith) (by linarith)
              have hw4 : (2140811/156250000000:ℝ) ≤ wfun (y + z) := wc_518 (y + z) (by linarith) (by linarith)
              have hw5 : (55096489/500000000000:ℝ) ≤ wfun (x + y + z) := wc_900 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (4087/2048:ℝ) with hc | hc
            · rcases le_total z (2131/2048:ℝ) with hc | hc
              · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
                have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_229 y (by linarith) (by linarith)
                have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                have hw3 : (55964847/10000000000000:ℝ) ≤ wfun (x + y) := wc_451 (x + y) (by linarith) (by linarith)
                have hw4 : (92247841/10000000000000:ℝ) ≤ wfun (y + z) := wc_481 (y + z) (by linarith) (by linarith)
                have hw5 : (8629543/78125000000:ℝ) ≤ wfun (x + y + z) := wc_899 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
                have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_229 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                have hw3 : (55964847/10000000000000:ℝ) ≤ wfun (x + y) := wc_451 (x + y) (by linarith) (by linarith)
                have hw4 : (13745521/1000000000000:ℝ) ≤ wfun (y + z) := wc_517 (y + z) (by linarith) (by linarith)
                have hw5 : (1208951451/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_926 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (2131/2048:ℝ) with hc | hc
              · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
                have hw1 : (1868712167/10000000000000:ℝ) ≤ wfun y := wc_232 y (by linarith) (by linarith)
                have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                have hw3 : (92247841/10000000000000:ℝ) ≤ wfun (x + y) := wc_481 (x + y) (by linarith) (by linarith)
                have hw4 : (13745521/1000000000000:ℝ) ≤ wfun (y + z) := wc_517 (y + z) (by linarith) (by linarith)
                have hw5 : (1208951451/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_926 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
                have hw1 : (1868712167/10000000000000:ℝ) ≤ wfun y := wc_232 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                have hw3 : (92247841/10000000000000:ℝ) ≤ wfun (x + y) := wc_481 (x + y) (by linarith) (by linarith)
                have hw4 : (23941523/1250000000000:ℝ) ≤ wfun (y + z) := wc_531 (y + z) (by linarith) (by linarith)
                have hw5 : (263549591/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_969 (x + y + z) (by linarith) (by linarith)
                linarith
    · rcases le_total y (2041/1024:ℝ) with hc | hc
      · rcases le_total z (1063/1024:ℝ) with hc | hc
        · rcases le_total x (2131/2048:ℝ) with hc | hc
          · rcases le_total y (4077/2048:ℝ) with hc | hc
            · rcases le_total z (2121/2048:ℝ) with hc | hc
              · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
                have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_217 y (by linarith) (by linarith)
                have hw2 : (1888462017/5000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
                have hw3 : (14329561/5000000000000:ℝ) ≤ wfun (x + y) := wc_419 (x + y) (by linarith) (by linarith)
                have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_361 (y + z) (by linarith) (by linarith)
                have hw5 : (12788137/156250000000:ℝ) ≤ wfun (x + y + z) := wc_847 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
                have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_217 y (by linarith) (by linarith)
                have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
                have hw3 : (14329561/5000000000000:ℝ) ≤ wfun (x + y) := wc_419 (x + y) (by linarith) (by linarith)
                have hw4 : (2076333/2000000000000:ℝ) ≤ wfun (y + z) := wc_389 (y + z) (by linarith) (by linarith)
                have hw5 : (56830383/625000000000:ℝ) ≤ wfun (x + y + z) := wc_860 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (2121/2048:ℝ) with hc | hc
              · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
                have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_226 y (by linarith) (by linarith)
                have hw2 : (1888462017/5000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
                have hw3 : (55964847/10000000000000:ℝ) ≤ wfun (x + y) := wc_451 (x + y) (by linarith) (by linarith)
                have hw4 : (2076333/2000000000000:ℝ) ≤ wfun (y + z) := wc_389 (y + z) (by linarith) (by linarith)
                have hw5 : (56830383/625000000000:ℝ) ≤ wfun (x + y + z) := wc_860 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
                have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_226 y (by linarith) (by linarith)
                have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
                have hw3 : (55964847/10000000000000:ℝ) ≤ wfun (x + y) := wc_451 (x + y) (by linarith) (by linarith)
                have hw4 : (14329561/5000000000000:ℝ) ≤ wfun (y + z) := wc_419 (y + z) (by linarith) (by linarith)
                have hw5 : (1004679561/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_874 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (4077/2048:ℝ) with hc | hc
            · rcases le_total z (2121/2048:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_31 x (by linarith) (by linarith)
                have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_217 y (by linarith) (by linarith)
                have hw2 : (1888462017/5000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
                have hw3 : (55964847/10000000000000:ℝ) ≤ wfun (x + y) := wc_451 (x + y) (by linarith) (by linarith)
                have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_361 (y + z) (by linarith) (by linarith)
                have hw5 : (56830383/625000000000:ℝ) ≤ wfun (x + y + z) := wc_860 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total x (4267/4096:ℝ) with hc | hc
                · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                  have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_217 y (by linarith) (by linarith)
                  have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
                  have hw3 : (28027757/5000000000000:ℝ) ≤ wfun (x + y) := wc_450 (x + y) (by linarith) (by linarith)
                  have hw4 : (2076333/2000000000000:ℝ) ≤ wfun (y + z) := wc_389 (y + z) (by linarith) (by linarith)
                  have hw5 : (1005888959/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_873 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                  have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_217 y (by linarith) (by linarith)
                  have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
                  have hw3 : (18276411/2500000000000:ℝ) ≤ wfun (x + y) := wc_466 (x + y) (by linarith) (by linarith)
                  have hw4 : (2076333/2000000000000:ℝ) ≤ wfun (y + z) := wc_389 (y + z) (by linarith) (by linarith)
                  have hw5 : (1055337947/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_889 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total z (2121/2048:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_31 x (by linarith) (by linarith)
                have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_226 y (by linarith) (by linarith)
                have hw2 : (1888462017/5000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
                have hw3 : (92247841/10000000000000:ℝ) ≤ wfun (x + y) := wc_481 (x + y) (by linarith) (by linarith)
                have hw4 : (2076333/2000000000000:ℝ) ≤ wfun (y + z) := wc_389 (y + z) (by linarith) (by linarith)
                have hw5 : (1004679561/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_874 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_31 x (by linarith) (by linarith)
                have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_226 y (by linarith) (by linarith)
                have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
                have hw3 : (92247841/10000000000000:ℝ) ≤ wfun (x + y) := wc_481 (x + y) (by linarith) (by linarith)
                have hw4 : (14329561/5000000000000:ℝ) ≤ wfun (y + z) := wc_419 (y + z) (by linarith) (by linarith)
                have hw5 : (8629543/78125000000:ℝ) ≤ wfun (x + y + z) := wc_899 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (2131/2048:ℝ) with hc | hc
          · rcases le_total y (4077/2048:ℝ) with hc | hc
            · rcases le_total z (2131/2048:ℝ) with hc | hc
              · rcases le_total x (4257/4096:ℝ) with hc | hc
                · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                  have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_217 y (by linarith) (by linarith)
                  have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                  have hw3 : (2870559/1000000000000:ℝ) ≤ wfun (x + y) := wc_418 (x + y) (by linarith) (by linarith)
                  have hw4 : (14329561/5000000000000:ℝ) ≤ wfun (y + z) := wc_419 (y + z) (by linarith) (by linarith)
                  have hw5 : (1005888959/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_873 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
                  have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_217 y (by linarith) (by linarith)
                  have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                  have hw3 : (20626673/5000000000000:ℝ) ≤ wfun (x + y) := wc_436 (x + y) (by linarith) (by linarith)
                  have hw4 : (14329561/5000000000000:ℝ) ≤ wfun (y + z) := wc_419 (y + z) (by linarith) (by linarith)
                  have hw5 : (1055337947/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_889 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total x (4257/4096:ℝ) with hc | hc
                · rcases le_total y (8149/4096:ℝ) with hc | hc
                  · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                    have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                    have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_417 (x + y) (by linarith) (by linarith)
                    have hw4 : (28027757/5000000000000:ℝ) ≤ wfun (y + z) := wc_450 (y + z) (by linarith) (by linarith)
                    have hw5 : (553620607/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_897 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                    have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                    have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_435 (x + y) (by linarith) (by linarith)
                    have hw4 : (18276411/2500000000000:ℝ) ≤ wfun (y + z) := wc_466 (y + z) (by linarith) (by linarith)
                    have hw5 : (1158993733/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_910 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total y (8149/4096:ℝ) with hc | hc
                  · rcases le_total z (4267/4096:ℝ) with hc | hc
                    · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
                      have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
                      have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                      have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_435 (x + y) (by linarith) (by linarith)
                      have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_449 (y + z) (by linarith) (by linarith)
                      have hw5 : (290097117/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_909 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
                      have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                      have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_435 (x + y) (by linarith) (by linarith)
                      have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_465 (y + z) (by linarith) (by linarith)
                      have hw5 : (1213318631/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_923 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
                    have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                    have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_449 (x + y) (by linarith) (by linarith)
                    have hw4 : (18276411/2500000000000:ℝ) ≤ wfun (y + z) := wc_466 (y + z) (by linarith) (by linarith)
                    have hw5 : (242372143/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_924 (x + y + z) (by linarith) (by linarith)
                    linarith
            · rcases le_total z (2131/2048:ℝ) with hc | hc
              · rcases le_total x (4257/4096:ℝ) with hc | hc
                · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                  have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_226 y (by linarith) (by linarith)
                  have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                  have hw3 : (28027757/5000000000000:ℝ) ≤ wfun (x + y) := wc_450 (x + y) (by linarith) (by linarith)
                  have hw4 : (55964847/10000000000000:ℝ) ≤ wfun (y + z) := wc_451 (y + z) (by linarith) (by linarith)
                  have hw5 : (1105910359/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_898 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
                  have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_226 y (by linarith) (by linarith)
                  have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                  have hw3 : (18276411/2500000000000:ℝ) ≤ wfun (x + y) := wc_466 (x + y) (by linarith) (by linarith)
                  have hw4 : (55964847/10000000000000:ℝ) ≤ wfun (y + z) := wc_451 (y + z) (by linarith) (by linarith)
                  have hw5 : (1157601093/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_911 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total x (4257/4096:ℝ) with hc | hc
                · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                  have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_226 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                  have hw3 : (28027757/5000000000000:ℝ) ≤ wfun (x + y) := wc_450 (x + y) (by linarith) (by linarith)
                  have hw4 : (92247841/10000000000000:ℝ) ≤ wfun (y + z) := wc_481 (y + z) (by linarith) (by linarith)
                  have hw5 : (121040499/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_925 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total y (8159/4096:ℝ) with hc | hc
                  · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
                    have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                    have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_465 (x + y) (by linarith) (by linarith)
                    have hw4 : (5774823/625000000000:ℝ) ≤ wfun (y + z) := wc_480 (y + z) (by linarith) (by linarith)
                    have hw5 : (1265836939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_947 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
                    have hw1 : (1245909663/5000000000000:ℝ) ≤ wfun y := wc_227 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                    have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_479 (x + y) (by linarith) (by linarith)
                    have hw4 : (569617/50000000000:ℝ) ≤ wfun (y + z) := wc_507 (y + z) (by linarith) (by linarith)
                    have hw5 : (660458559/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_967 (x + y + z) (by linarith) (by linarith)
                    linarith
          · rcases le_total y (4077/2048:ℝ) with hc | hc
            · rcases le_total z (2131/2048:ℝ) with hc | hc
              · rcases le_total x (4267/4096:ℝ) with hc | hc
                · rcases le_total y (8149/4096:ℝ) with hc | hc
                  · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                    have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
                    have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                    have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_449 (x + y) (by linarith) (by linarith)
                    have hw4 : (2870559/1000000000000:ℝ) ≤ wfun (y + z) := wc_418 (y + z) (by linarith) (by linarith)
                    have hw5 : (553620607/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_897 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                    have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
                    have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                    have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_465 (x + y) (by linarith) (by linarith)
                    have hw4 : (20626673/5000000000000:ℝ) ≤ wfun (y + z) := wc_436 (y + z) (by linarith) (by linarith)
                    have hw5 : (1158993733/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_910 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total y (8149/4096:ℝ) with hc | hc
                  · rcases le_total z (4257/4096:ℝ) with hc | hc
                    · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                      have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
                      have hw2 : (2586175977/10000000000000:ℝ) ≤ wfun z := wc_23 z (by linarith) (by linarith)
                      have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_465 (x + y) (by linarith) (by linarith)
                      have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_417 (y + z) (by linarith) (by linarith)
                      have hw5 : (290097117/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_909 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                      have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
                      have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
                      have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_465 (x + y) (by linarith) (by linarith)
                      have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_435 (y + z) (by linarith) (by linarith)
                      have hw5 : (1213318631/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_923 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                    have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
                    have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                    have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_479 (x + y) (by linarith) (by linarith)
                    have hw4 : (20626673/5000000000000:ℝ) ≤ wfun (y + z) := wc_436 (y + z) (by linarith) (by linarith)
                    have hw5 : (242372143/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_924 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total x (4267/4096:ℝ) with hc | hc
                · rcases le_total y (8149/4096:ℝ) with hc | hc
                  · rcases le_total z (4267/4096:ℝ) with hc | hc
                    · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                      have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
                      have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                      have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_449 (x + y) (by linarith) (by linarith)
                      have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_449 (y + z) (by linarith) (by linarith)
                      have hw5 : (1213318631/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_923 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                      have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                      have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_449 (x + y) (by linarith) (by linarith)
                      have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_465 (y + z) (by linarith) (by linarith)
                      have hw5 : (1267359331/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_946 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · rcases le_total z (4267/4096:ℝ) with hc | hc
                    · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                      have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
                      have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                      have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_465 (x + y) (by linarith) (by linarith)
                      have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_465 (y + z) (by linarith) (by linarith)
                      have hw5 : (1267359331/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_946 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                      have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                      have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_465 (x + y) (by linarith) (by linarith)
                      have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_479 (y + z) (by linarith) (by linarith)
                      have hw5 : (52900211/400000000000:ℝ) ≤ wfun (x + y + z) := wc_966 (x + y + z) (by linarith) (by linarith)
                      linarith
                · rcases le_total y (8149/4096:ℝ) with hc | hc
                  · rcases le_total z (4267/4096:ℝ) with hc | hc
                    · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                      have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
                      have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                      have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_465 (x + y) (by linarith) (by linarith)
                      have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_449 (y + z) (by linarith) (by linarith)
                      have hw5 : (1267359331/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_946 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · rcases le_total x (8539/8192:ℝ) with hc | hc
                      · have hw0 : (1770787537/10000000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
                        have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
                        have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                        have hw3 : (73283389/10000000000000:ℝ) ≤ wfun (x + y) := wc_464 (x + y) (by linarith) (by linarith)
                        have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_465 (y + z) (by linarith) (by linarith)
                        have hw5 : (1323300249/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_965 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                        have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
                        have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                        have hw3 : (82672123/10000000000000:ℝ) ≤ wfun (x + y) := wc_472 (x + y) (by linarith) (by linarith)
                        have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_465 (y + z) (by linarith) (by linarith)
                        have hw5 : (1351302719/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_980 (x + y + z) (by linarith) (by linarith)
                        linarith
                  · rcases le_total z (4267/4096:ℝ) with hc | hc
                    · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                      have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
                      have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                      have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_479 (x + y) (by linarith) (by linarith)
                      have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_465 (y + z) (by linarith) (by linarith)
                      have hw5 : (52900211/400000000000:ℝ) ≤ wfun (x + y + z) := wc_966 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · rcases le_total x (8539/8192:ℝ) with hc | hc
                      · have hw0 : (1770787537/10000000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
                        have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
                        have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                        have hw3 : (46310863/5000000000000:ℝ) ≤ wfun (x + y) := wc_478 (x + y) (by linarith) (by linarith)
                        have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_479 (y + z) (by linarith) (by linarith)
                        have hw5 : (1379579649/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_989 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                        have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
                        have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                        have hw3 : (25782839/2500000000000:ℝ) ≤ wfun (x + y) := wc_499 (x + y) (by linarith) (by linarith)
                        have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_479 (y + z) (by linarith) (by linarith)
                        have hw5 : (1408130363/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1001 (x + y + z) (by linarith) (by linarith)
                        linarith
            · rcases le_total z (2131/2048:ℝ) with hc | hc
              · rcases le_total x (4267/4096:ℝ) with hc | hc
                · rcases le_total y (8159/4096:ℝ) with hc | hc
                  · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                    have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
                    have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                    have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_479 (x + y) (by linarith) (by linarith)
                    have hw4 : (28027757/5000000000000:ℝ) ≤ wfun (y + z) := wc_450 (y + z) (by linarith) (by linarith)
                    have hw5 : (242372143/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_924 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                    have hw1 : (1245909663/5000000000000:ℝ) ≤ wfun y := wc_227 y (by linarith) (by linarith)
                    have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                    have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_506 (x + y) (by linarith) (by linarith)
                    have hw4 : (18276411/2500000000000:ℝ) ≤ wfun (y + z) := wc_466 (y + z) (by linarith) (by linarith)
                    have hw5 : (1265836939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_947 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total y (8159/4096:ℝ) with hc | hc
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                    have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
                    have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                    have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_506 (x + y) (by linarith) (by linarith)
                    have hw4 : (28027757/5000000000000:ℝ) ≤ wfun (y + z) := wc_450 (y + z) (by linarith) (by linarith)
                    have hw5 : (1265836939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_947 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                    have hw1 : (1245909663/5000000000000:ℝ) ≤ wfun y := wc_227 y (by linarith) (by linarith)
                    have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                    have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_515 (x + y) (by linarith) (by linarith)
                    have hw4 : (18276411/2500000000000:ℝ) ≤ wfun (y + z) := wc_466 (y + z) (by linarith) (by linarith)
                    have hw5 : (660458559/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_967 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total x (4267/4096:ℝ) with hc | hc
                · rcases le_total y (8159/4096:ℝ) with hc | hc
                  · rcases le_total z (4267/4096:ℝ) with hc | hc
                    · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                      have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
                      have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                      have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_479 (x + y) (by linarith) (by linarith)
                      have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_479 (y + z) (by linarith) (by linarith)
                      have hw5 : (52900211/400000000000:ℝ) ≤ wfun (x + y + z) := wc_966 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                      have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                      have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_479 (x + y) (by linarith) (by linarith)
                      have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_506 (y + z) (by linarith) (by linarith)
                      have hw5 : (275750223/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_990 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                    have hw1 : (1245909663/5000000000000:ℝ) ≤ wfun y := wc_227 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                    have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_506 (x + y) (by linarith) (by linarith)
                    have hw4 : (569617/50000000000:ℝ) ≤ wfun (y + z) := wc_507 (y + z) (by linarith) (by linarith)
                    have hw5 : (172136989/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_991 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total y (8159/4096:ℝ) with hc | hc
                  · rcases le_total z (4267/4096:ℝ) with hc | hc
                    · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                      have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
                      have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                      have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_506 (x + y) (by linarith) (by linarith)
                      have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_479 (y + z) (by linarith) (by linarith)
                      have hw5 : (275750223/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_990 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                      have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                      have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_506 (x + y) (by linarith) (by linarith)
                      have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_506 (y + z) (by linarith) (by linarith)
                      have hw5 : (718045723/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1011 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · rcases le_total z (4267/4096:ℝ) with hc | hc
                    · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                      have hw1 : (1245909663/5000000000000:ℝ) ≤ wfun y := wc_227 y (by linarith) (by linarith)
                      have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                      have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_515 (x + y) (by linarith) (by linarith)
                      have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_506 (y + z) (by linarith) (by linarith)
                      have hw5 : (718045723/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1011 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                      have hw1 : (1245909663/5000000000000:ℝ) ≤ wfun y := wc_227 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                      have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_515 (x + y) (by linarith) (by linarith)
                      have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
                      have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1044 (x + y + z) (by linarith) (by linarith)
                      linarith
      · rcases le_total z (1063/1024:ℝ) with hc | hc
        · rcases le_total x (2131/2048:ℝ) with hc | hc
          · rcases le_total y (4087/2048:ℝ) with hc | hc
            · rcases le_total z (2121/2048:ℝ) with hc | hc
              · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
                have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_229 y (by linarith) (by linarith)
                have hw2 : (1888462017/5000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
                have hw3 : (92247841/10000000000000:ℝ) ≤ wfun (x + y) := wc_481 (x + y) (by linarith) (by linarith)
                have hw4 : (14329561/5000000000000:ℝ) ≤ wfun (y + z) := wc_419 (y + z) (by linarith) (by linarith)
                have hw5 : (1004679561/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_874 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
                have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_229 y (by linarith) (by linarith)
                have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
                have hw3 : (92247841/10000000000000:ℝ) ≤ wfun (x + y) := wc_481 (x + y) (by linarith) (by linarith)
                have hw4 : (55964847/10000000000000:ℝ) ≤ wfun (y + z) := wc_451 (y + z) (by linarith) (by linarith)
                have hw5 : (8629543/78125000000:ℝ) ≤ wfun (x + y + z) := wc_899 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
              have hw1 : (1868712167/10000000000000:ℝ) ≤ wfun y := wc_232 y (by linarith) (by linarith)
              have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
              have hw3 : (13745521/1000000000000:ℝ) ≤ wfun (x + y) := wc_517 (x + y) (by linarith) (by linarith)
              have hw4 : (27892031/5000000000000:ℝ) ≤ wfun (y + z) := wc_452 (y + z) (by linarith) (by linarith)
              have hw5 : (55096489/500000000000:ℝ) ≤ wfun (x + y + z) := wc_900 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (4087/2048:ℝ) with hc | hc
            · rcases le_total z (2121/2048:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_31 x (by linarith) (by linarith)
                have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_229 y (by linarith) (by linarith)
                have hw2 : (1888462017/5000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
                have hw3 : (13745521/1000000000000:ℝ) ≤ wfun (x + y) := wc_517 (x + y) (by linarith) (by linarith)
                have hw4 : (14329561/5000000000000:ℝ) ≤ wfun (y + z) := wc_419 (y + z) (by linarith) (by linarith)
                have hw5 : (8629543/78125000000:ℝ) ≤ wfun (x + y + z) := wc_899 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_31 x (by linarith) (by linarith)
                have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_229 y (by linarith) (by linarith)
                have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
                have hw3 : (13745521/1000000000000:ℝ) ≤ wfun (x + y) := wc_517 (x + y) (by linarith) (by linarith)
                have hw4 : (55964847/10000000000000:ℝ) ≤ wfun (y + z) := wc_451 (y + z) (by linarith) (by linarith)
                have hw5 : (1208951451/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_926 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (2121/2048:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_31 x (by linarith) (by linarith)
                have hw1 : (1868712167/10000000000000:ℝ) ≤ wfun y := wc_232 y (by linarith) (by linarith)
                have hw2 : (1888462017/5000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
                have hw3 : (23941523/1250000000000:ℝ) ≤ wfun (x + y) := wc_531 (x + y) (by linarith) (by linarith)
                have hw4 : (55964847/10000000000000:ℝ) ≤ wfun (y + z) := wc_451 (y + z) (by linarith) (by linarith)
                have hw5 : (1208951451/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_926 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_31 x (by linarith) (by linarith)
                have hw1 : (1868712167/10000000000000:ℝ) ≤ wfun y := wc_232 y (by linarith) (by linarith)
                have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
                have hw3 : (23941523/1250000000000:ℝ) ≤ wfun (x + y) := wc_531 (x + y) (by linarith) (by linarith)
                have hw4 : (92247841/10000000000000:ℝ) ≤ wfun (y + z) := wc_481 (y + z) (by linarith) (by linarith)
                have hw5 : (263549591/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_969 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (2131/2048:ℝ) with hc | hc
          · rcases le_total y (4087/2048:ℝ) with hc | hc
            · rcases le_total z (2131/2048:ℝ) with hc | hc
              · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
                have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_229 y (by linarith) (by linarith)
                have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                have hw3 : (92247841/10000000000000:ℝ) ≤ wfun (x + y) := wc_481 (x + y) (by linarith) (by linarith)
                have hw4 : (92247841/10000000000000:ℝ) ≤ wfun (y + z) := wc_481 (y + z) (by linarith) (by linarith)
                have hw5 : (1208951451/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_926 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total x (4257/4096:ℝ) with hc | hc
                · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                  have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_229 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                  have hw3 : (5774823/625000000000:ℝ) ≤ wfun (x + y) := wc_480 (x + y) (by linarith) (by linarith)
                  have hw4 : (13745521/1000000000000:ℝ) ≤ wfun (y + z) := wc_517 (y + z) (by linarith) (by linarith)
                  have hw5 : (659665673/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_968 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
                  have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_229 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                  have hw3 : (569617/50000000000:ℝ) ≤ wfun (x + y) := wc_507 (x + y) (by linarith) (by linarith)
                  have hw4 : (13745521/1000000000000:ℝ) ≤ wfun (y + z) := wc_517 (y + z) (by linarith) (by linarith)
                  have hw5 : (275088639/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_992 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total z (2131/2048:ℝ) with hc | hc
              · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
                have hw1 : (1868712167/10000000000000:ℝ) ≤ wfun y := wc_232 y (by linarith) (by linarith)
                have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                have hw3 : (13745521/1000000000000:ℝ) ≤ wfun (x + y) := wc_517 (x + y) (by linarith) (by linarith)
                have hw4 : (13745521/1000000000000:ℝ) ≤ wfun (y + z) := wc_517 (y + z) (by linarith) (by linarith)
                have hw5 : (263549591/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_969 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
                have hw1 : (1868712167/10000000000000:ℝ) ≤ wfun y := wc_232 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                have hw3 : (13745521/1000000000000:ℝ) ≤ wfun (x + y) := wc_517 (x + y) (by linarith) (by linarith)
                have hw4 : (23941523/1250000000000:ℝ) ≤ wfun (y + z) := wc_531 (y + z) (by linarith) (by linarith)
                have hw5 : (715464319/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1014 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (4087/2048:ℝ) with hc | hc
            · rcases le_total z (2131/2048:ℝ) with hc | hc
              · rcases le_total x (4267/4096:ℝ) with hc | hc
                · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                  have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_229 y (by linarith) (by linarith)
                  have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                  have hw3 : (4302423/312500000000:ℝ) ≤ wfun (x + y) := wc_516 (x + y) (by linarith) (by linarith)
                  have hw4 : (92247841/10000000000000:ℝ) ≤ wfun (y + z) := wc_481 (y + z) (by linarith) (by linarith)
                  have hw5 : (659665673/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_968 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                  have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_229 y (by linarith) (by linarith)
                  have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                  have hw3 : (163652657/10000000000000:ℝ) ≤ wfun (x + y) := wc_524 (x + y) (by linarith) (by linarith)
                  have hw4 : (92247841/10000000000000:ℝ) ≤ wfun (y + z) := wc_481 (y + z) (by linarith) (by linarith)
                  have hw5 : (275088639/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_992 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total x (4267/4096:ℝ) with hc | hc
                · rcases le_total y (8169/4096:ℝ) with hc | hc
                  · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                    have hw1 : (2327527631/10000000000000:ℝ) ≤ wfun y := wc_228 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                    have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_515 (x + y) (by linarith) (by linarith)
                    have hw4 : (4302423/312500000000:ℝ) ≤ wfun (y + z) := wc_516 (y + z) (by linarith) (by linarith)
                    have hw5 : (57374717/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1012 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                    have hw1 : (2168970253/10000000000000:ℝ) ≤ wfun y := wc_231 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                    have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_523 (x + y) (by linarith) (by linarith)
                    have hw4 : (163652657/10000000000000:ℝ) ≤ wfun (y + z) := wc_524 (y + z) (by linarith) (by linarith)
                    have hw5 : (1492727701/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1045 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total y (8169/4096:ℝ) with hc | hc
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                    have hw1 : (2327527631/10000000000000:ℝ) ≤ wfun y := wc_228 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                    have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_523 (x + y) (by linarith) (by linarith)
                    have hw4 : (4302423/312500000000:ℝ) ≤ wfun (y + z) := wc_516 (y + z) (by linarith) (by linarith)
                    have hw5 : (1492727701/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1045 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                    have hw1 : (2168970253/10000000000000:ℝ) ≤ wfun y := wc_231 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                    have hw3 : (192151891/10000000000000:ℝ) ≤ wfun (x + y) := wc_529 (x + y) (by linarith) (by linarith)
                    have hw4 : (163652657/10000000000000:ℝ) ≤ wfun (y + z) := wc_524 (y + z) (by linarith) (by linarith)
                    have hw5 : (62086789/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1066 (x + y + z) (by linarith) (by linarith)
                    linarith
            · rcases le_total z (2131/2048:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_31 x (by linarith) (by linarith)
                have hw1 : (1868712167/10000000000000:ℝ) ≤ wfun y := wc_232 y (by linarith) (by linarith)
                have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                have hw3 : (23941523/1250000000000:ℝ) ≤ wfun (x + y) := wc_531 (x + y) (by linarith) (by linarith)
                have hw4 : (13745521/1000000000000:ℝ) ≤ wfun (y + z) := wc_517 (y + z) (by linarith) (by linarith)
                have hw5 : (715464319/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1014 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total x (4267/4096:ℝ) with hc | hc
                · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                  have hw1 : (1868712167/10000000000000:ℝ) ≤ wfun y := wc_232 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                  have hw3 : (47960431/2500000000000:ℝ) ≤ wfun (x + y) := wc_530 (x + y) (by linarith) (by linarith)
                  have hw4 : (23941523/1250000000000:ℝ) ≤ wfun (y + z) := wc_531 (y + z) (by linarith) (by linarith)
                  have hw5 : (775154287/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1067 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                  have hw1 : (1868712167/10000000000000:ℝ) ≤ wfun y := wc_232 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                  have hw3 : (111118793/5000000000000:ℝ) ≤ wfun (x + y) := wc_540 (x + y) (by linarith) (by linarith)
                  have hw4 : (23941523/1250000000000:ℝ) ≤ wfun (y + z) := wc_531 (y + z) (by linarith) (by linarith)
                  have hw5 : (1610755299/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1088 (x + y + z) (by linarith) (by linarith)
                  linarith

set_option maxHeartbeats 20000000 in
lemma ch_40 (x y z : ℝ) (hx1 : (267/256:ℝ) ≤ x) (hx2 : x ≤ (1073/1024:ℝ))
    (hy1 : (63/32:ℝ) ≤ y) (hy2 : y ≤ (1013/512:ℝ))
    (hz1 : (529/512:ℝ) ≤ z) (hz2 : z ≤ (267/256:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total y (2021/1024:ℝ) with hc | hc
  · rcases le_total z (1063/1024:ℝ) with hc | hc
    · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
      have hw1 : (2946158453/5000000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
      have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
      have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := wc_329 (y + z) (by linarith) (by linarith)
      have hw5 : (184146301/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_802 (x + y + z) (by linarith) (by linarith)
      linarith
    · rcases le_total x (2141/2048:ℝ) with hc | hc
      · rcases le_total y (4037/2048:ℝ) with hc | hc
        · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
          have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_130 y (by linarith) (by linarith)
          have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
          have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_339 (x + y) (by linarith) (by linarith)
          have hw4 : (3586667/1250000000000:ℝ) ≤ wfun (y + z) := wc_334 (y + z) (by linarith) (by linarith)
          have hw5 : (20003551/400000000000:ℝ) ≤ wfun (x + y + z) := wc_811 (x + y + z) (by linarith) (by linarith)
          linarith
        · rcases le_total z (2131/2048:ℝ) with hc | hc
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
            have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_137 y (by linarith) (by linarith)
            have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
            have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_345 (x + y) (by linarith) (by linarith)
            have hw4 : (3586667/1250000000000:ℝ) ≤ wfun (y + z) := wc_336 (y + z) (by linarith) (by linarith)
            have hw5 : (573574207/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_816 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (4277/4096:ℝ) with hc | hc
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
              have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_137 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
              have hw3 : (906687/2000000000000:ℝ) ≤ wfun (x + y) := wc_344 (x + y) (by linarith) (by linarith)
              have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_339 (y + z) (by linarith) (by linarith)
              have hw5 : (325666339/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_819 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
              have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_137 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
              have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_347 (x + y) (by linarith) (by linarith)
              have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_339 (y + z) (by linarith) (by linarith)
              have hw5 : (69161783/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_835 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total y (4037/2048:ℝ) with hc | hc
        · rcases le_total z (2131/2048:ℝ) with hc | hc
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_56 x (by linarith) (by linarith)
            have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_130 y (by linarith) (by linarith)
            have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
            have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_345 (x + y) (by linarith) (by linarith)
            have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := wc_333 (y + z) (by linarith) (by linarith)
            have hw5 : (573574207/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_816 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_56 x (by linarith) (by linarith)
            have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_130 y (by linarith) (by linarith)
            have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
            have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_345 (x + y) (by linarith) (by linarith)
            have hw4 : (3586667/1250000000000:ℝ) ≤ wfun (y + z) := wc_336 (y + z) (by linarith) (by linarith)
            have hw5 : (162636919/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_820 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (2131/2048:ℝ) with hc | hc
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_56 x (by linarith) (by linarith)
            have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_137 y (by linarith) (by linarith)
            have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
            have hw4 : (3586667/1250000000000:ℝ) ≤ wfun (y + z) := wc_336 (y + z) (by linarith) (by linarith)
            have hw5 : (162636919/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_820 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (4287/4096:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
              have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_137 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
              have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_339 (y + z) (by linarith) (by linarith)
              have hw5 : (14661301/200000000000:ℝ) ≤ wfun (x + y + z) := wc_838 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total y (8079/4096:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
                have hw1 : (6172561523/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                have hw4 : (18318183/10000000000000:ℝ) ≤ wfun (y + z) := wc_338 (y + z) (by linarith) (by linarith)
                have hw5 : (388302571/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_842 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
                have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_139 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_342 (y + z) (by linarith) (by linarith)
                have hw5 : (820415059/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_845 (x + y + z) (by linarith) (by linarith)
                linarith
  · rcases le_total z (1063/1024:ℝ) with hc | hc
    · rcases le_total x (2141/2048:ℝ) with hc | hc
      · rcases le_total y (4047/2048:ℝ) with hc | hc
        · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
          have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
          have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
          have hw4 : (3586667/1250000000000:ℝ) ≤ wfun (y + z) := wc_334 (y + z) (by linarith) (by linarith)
          have hw5 : (20003551/400000000000:ℝ) ≤ wfun (x + y + z) := wc_811 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
          have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_151 y (by linarith) (by linarith)
          have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
          have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_337 (y + z) (by linarith) (by linarith)
          have hw5 : (572192259/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_817 (x + y + z) (by linarith) (by linarith)
          linarith
      · rcases le_total y (4047/2048:ℝ) with hc | hc
        · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_56 x (by linarith) (by linarith)
          have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
          have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
          have hw4 : (3586667/1250000000000:ℝ) ≤ wfun (y + z) := wc_334 (y + z) (by linarith) (by linarith)
          have hw5 : (572192259/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_817 (x + y + z) (by linarith) (by linarith)
          linarith
        · rcases le_total z (2121/2048:ℝ) with hc | hc
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_56 x (by linarith) (by linarith)
            have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_151 y (by linarith) (by linarith)
            have hw2 : (1888462017/5000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
            have hw3 : (1181561/10000000000000:ℝ) ≤ wfun (x + y) := wc_361 (x + y) (by linarith) (by linarith)
            have hw4 : (3586667/1250000000000:ℝ) ≤ wfun (y + z) := wc_336 (y + z) (by linarith) (by linarith)
            have hw5 : (162636919/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_820 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_56 x (by linarith) (by linarith)
            have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_151 y (by linarith) (by linarith)
            have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
            have hw3 : (1181561/10000000000000:ℝ) ≤ wfun (x + y) := wc_361 (x + y) (by linarith) (by linarith)
            have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_339 (y + z) (by linarith) (by linarith)
            have hw5 : (183045519/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_839 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total x (2141/2048:ℝ) with hc | hc
      · rcases le_total y (4047/2048:ℝ) with hc | hc
        · rcases le_total z (2131/2048:ℝ) with hc | hc
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
            have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
            have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
            have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_339 (y + z) (by linarith) (by linarith)
            have hw5 : (162636919/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_820 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (4277/4096:ℝ) with hc | hc
            · rcases le_total y (8089/4096:ℝ) with hc | hc
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_348 (x + y) (by linarith) (by linarith)
                have hw4 : (906687/2000000000000:ℝ) ≤ wfun (y + z) := wc_344 (y + z) (by linarith) (by linarith)
                have hw5 : (733949357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_837 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_347 (y + z) (by linarith) (by linarith)
                have hw5 : (388302571/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_842 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (8089/4096:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                have hw4 : (906687/2000000000000:ℝ) ≤ wfun (y + z) := wc_344 (y + z) (by linarith) (by linarith)
                have hw5 : (388302571/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_842 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_347 (y + z) (by linarith) (by linarith)
                have hw5 : (820415059/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_845 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (2131/2048:ℝ) with hc | hc
          · rcases le_total x (4277/4096:ℝ) with hc | hc
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
              have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_151 y (by linarith) (by linarith)
              have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
              have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_345 (y + z) (by linarith) (by linarith)
              have hw5 : (14661301/200000000000:ℝ) ≤ wfun (x + y + z) := wc_838 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total y (8099/4096:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
                have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_353 (x + y) (by linarith) (by linarith)
                have hw4 : (906687/2000000000000:ℝ) ≤ wfun (y + z) := wc_344 (y + z) (by linarith) (by linarith)
                have hw5 : (388302571/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_842 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
                have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_359 (x + y) (by linarith) (by linarith)
                have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_347 (y + z) (by linarith) (by linarith)
                have hw5 : (820415059/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_845 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (4277/4096:ℝ) with hc | hc
            · rcases le_total y (8099/4096:ℝ) with hc | hc
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                have hw5 : (820415059/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_845 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total z (4267/4096:ℝ) with hc | hc
                · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                  have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
                  have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                  have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_353 (x + y) (by linarith) (by linarith)
                  have hw5 : (866417641/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_854 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                  have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                  have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_353 (x + y) (by linarith) (by linarith)
                  have hw5 : (3564753/39062500000:ℝ) ≤ wfun (x + y + z) := wc_857 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total y (8099/4096:ℝ) with hc | hc
              · rcases le_total z (4267/4096:ℝ) with hc | hc
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                  have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
                  have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                  have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_353 (x + y) (by linarith) (by linarith)
                  have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_348 (y + z) (by linarith) (by linarith)
                  have hw5 : (866417641/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_854 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                  have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                  have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_353 (x + y) (by linarith) (by linarith)
                  have hw5 : (3564753/39062500000:ℝ) ≤ wfun (x + y + z) := wc_857 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (4267/4096:ℝ) with hc | hc
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                  have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
                  have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                  have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_359 (x + y) (by linarith) (by linarith)
                  have hw5 : (3564753/39062500000:ℝ) ≤ wfun (x + y + z) := wc_857 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total x (8559/8192:ℝ) with hc | hc
                  · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                    have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                    have hw3 : (593183/5000000000000:ℝ) ≤ wfun (x + y) := wc_358 (x + y) (by linarith) (by linarith)
                    have hw5 : (192091031/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_864 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                    have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                    have hw3 : (2638657/10000000000000:ℝ) ≤ wfun (x + y) := wc_369 (x + y) (by linarith) (by linarith)
                    have hw5 : (984546007/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_868 (x + y + z) (by linarith) (by linarith)
                    linarith
      · rcases le_total y (4047/2048:ℝ) with hc | hc
        · rcases le_total z (2131/2048:ℝ) with hc | hc
          · rcases le_total x (4287/4096:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
              have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
              have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
              have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_339 (y + z) (by linarith) (by linarith)
              have hw5 : (14661301/200000000000:ℝ) ≤ wfun (x + y + z) := wc_838 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
              have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
              have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
              have hw3 : (41/1250000000000:ℝ) ≤ wfun (x + y) := wc_354 (x + y) (by linarith) (by linarith)
              have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_339 (y + z) (by linarith) (by linarith)
              have hw5 : (193917431/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_843 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (4287/4096:ℝ) with hc | hc
            · rcases le_total y (8089/4096:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
                have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                have hw4 : (906687/2000000000000:ℝ) ≤ wfun (y + z) := wc_344 (y + z) (by linarith) (by linarith)
                have hw5 : (820415059/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_845 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total z (4267/4096:ℝ) with hc | hc
                · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
                  have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
                  have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                  have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_353 (x + y) (by linarith) (by linarith)
                  have hw4 : (906687/2000000000000:ℝ) ≤ wfun (y + z) := wc_346 (y + z) (by linarith) (by linarith)
                  have hw5 : (866417641/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_854 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
                  have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                  have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_353 (x + y) (by linarith) (by linarith)
                  have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_348 (y + z) (by linarith) (by linarith)
                  have hw5 : (3564753/39062500000:ℝ) ≤ wfun (x + y + z) := wc_857 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total y (8089/4096:ℝ) with hc | hc
              · rcases le_total z (4267/4096:ℝ) with hc | hc
                · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
                  have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
                  have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                  have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_353 (x + y) (by linarith) (by linarith)
                  have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_343 (y + z) (by linarith) (by linarith)
                  have hw5 : (866417641/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_854 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
                  have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                  have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_353 (x + y) (by linarith) (by linarith)
                  have hw4 : (906687/2000000000000:ℝ) ≤ wfun (y + z) := wc_346 (y + z) (by linarith) (by linarith)
                  have hw5 : (3564753/39062500000:ℝ) ≤ wfun (x + y + z) := wc_857 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (4267/4096:ℝ) with hc | hc
                · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
                  have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
                  have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                  have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_359 (x + y) (by linarith) (by linarith)
                  have hw4 : (906687/2000000000000:ℝ) ≤ wfun (y + z) := wc_346 (y + z) (by linarith) (by linarith)
                  have hw5 : (3564753/39062500000:ℝ) ≤ wfun (x + y + z) := wc_857 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
                  have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                  have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_359 (x + y) (by linarith) (by linarith)
                  have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_348 (y + z) (by linarith) (by linarith)
                  have hw5 : (959876941/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_865 (x + y + z) (by linarith) (by linarith)
                  linarith
        · rcases le_total z (2131/2048:ℝ) with hc | hc
          · rcases le_total x (4287/4096:ℝ) with hc | hc
            · rcases le_total y (8099/4096:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
                have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
                have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_359 (x + y) (by linarith) (by linarith)
                have hw4 : (906687/2000000000000:ℝ) ≤ wfun (y + z) := wc_344 (y + z) (by linarith) (by linarith)
                have hw5 : (820415059/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_845 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
                have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
                have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_374 (x + y) (by linarith) (by linarith)
                have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_347 (y + z) (by linarith) (by linarith)
                have hw5 : (865374359/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_855 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (8099/4096:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
                have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
                have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_374 (x + y) (by linarith) (by linarith)
                have hw4 : (906687/2000000000000:ℝ) ≤ wfun (y + z) := wc_344 (y + z) (by linarith) (by linarith)
                have hw5 : (865374359/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_855 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
                have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
                have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_387 (x + y) (by linarith) (by linarith)
                have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_347 (y + z) (by linarith) (by linarith)
                have hw5 : (227869559/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_858 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (4287/4096:ℝ) with hc | hc
            · rcases le_total y (8099/4096:ℝ) with hc | hc
              · rcases le_total z (4267/4096:ℝ) with hc | hc
                · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
                  have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
                  have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                  have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_359 (x + y) (by linarith) (by linarith)
                  have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_348 (y + z) (by linarith) (by linarith)
                  have hw5 : (3564753/39062500000:ℝ) ≤ wfun (x + y + z) := wc_857 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total x (8569/8192:ℝ) with hc | hc
                  · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                    have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                    have hw3 : (593183/5000000000000:ℝ) ≤ wfun (x + y) := wc_358 (x + y) (by linarith) (by linarith)
                    have hw5 : (192091031/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_864 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
                    have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                    have hw3 : (2638657/10000000000000:ℝ) ≤ wfun (x + y) := wc_369 (x + y) (by linarith) (by linarith)
                    have hw5 : (984546007/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_868 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total z (4267/4096:ℝ) with hc | hc
                · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
                  have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
                  have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                  have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_374 (x + y) (by linarith) (by linarith)
                  have hw5 : (959876941/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_865 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total x (8569/8192:ℝ) with hc | hc
                  · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                    have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                    have hw3 : (4662827/10000000000000:ℝ) ≤ wfun (x + y) := wc_373 (x + y) (by linarith) (by linarith)
                    have hw5 : (1008920431/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_870 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · rcases le_total y (16203/8192:ℝ) with hc | hc
                    · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
                      have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                      have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
                      have hw5 : (517100111/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_883 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
                      have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                      have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
                      have hw5 : (264788707/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_885 (x + y + z) (by linarith) (by linarith)
                      linarith
            · rcases le_total y (8099/4096:ℝ) with hc | hc
              · rcases le_total z (4267/4096:ℝ) with hc | hc
                · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
                  have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
                  have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                  have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_374 (x + y) (by linarith) (by linarith)
                  have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_348 (y + z) (by linarith) (by linarith)
                  have hw5 : (959876941/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_865 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total x (8579/8192:ℝ) with hc | hc
                  · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
                    have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                    have hw3 : (4662827/10000000000000:ℝ) ≤ wfun (x + y) := wc_373 (x + y) (by linarith) (by linarith)
                    have hw5 : (1008920431/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_870 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
                    have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                    have hw3 : (7258139/10000000000000:ℝ) ≤ wfun (x + y) := wc_380 (x + y) (by linarith) (by linarith)
                    have hw5 : (5167889/50000000000:ℝ) ≤ wfun (x + y + z) := wc_884 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total z (4267/4096:ℝ) with hc | hc
                · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
                  have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
                  have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                  have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_387 (x + y) (by linarith) (by linarith)
                  have hw5 : (126039153/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_871 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total x (8579/8192:ℝ) with hc | hc
                  · rcases le_total y (16203/8192:ℝ) with hc | hc
                    · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
                      have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                      have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
                      have hw5 : (264788707/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_885 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
                      have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                      have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
                      have hw5 : (13554891/125000000000:ℝ) ≤ wfun (x + y + z) := wc_891 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · rcases le_total y (16203/8192:ℝ) with hc | hc
                    · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
                      have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                      have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
                      have hw5 : (13554891/125000000000:ℝ) ≤ wfun (x + y + z) := wc_891 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
                      have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                      have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
                      have hw5 : (1109908939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_894 (x + y + z) (by linarith) (by linarith)
                      linarith

set_option maxHeartbeats 20000000 in
lemma ch_52 (x y z : ℝ) (hx1 : (2151/2048:ℝ) ≤ x) (hx2 : x ≤ (539/512:ℝ))
    (hy1 : (1013/512:ℝ) ≤ y) (hy2 : y ≤ (2031/1024:ℝ))
    (hz1 : (1063/1024:ℝ) ≤ z) (hz2 : z ≤ (267/256:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total y (4057/2048:ℝ) with hc | hc
  · rcases le_total z (2131/2048:ℝ) with hc | hc
    · rcases le_total x (4307/4096:ℝ) with hc | hc
      · rcases le_total y (8109/4096:ℝ) with hc | hc
        · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
          have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_162 y (by linarith) (by linarith)
          have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
          have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_449 (x + y) (by linarith) (by linarith)
          have hw5 : (553620607/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_897 (x + y + z) (by linarith) (by linarith)
          linarith
        · rcases le_total z (4257/4096:ℝ) with hc | hc
          · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
            have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_172 y (by linarith) (by linarith)
            have hw2 : (2586175977/10000000000000:ℝ) ≤ wfun z := wc_23 z (by linarith) (by linarith)
            have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_465 (x + y) (by linarith) (by linarith)
            have hw5 : (290097117/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_909 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
            have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_172 y (by linarith) (by linarith)
            have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
            have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_465 (x + y) (by linarith) (by linarith)
            have hw5 : (1213318631/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_923 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total y (8109/4096:ℝ) with hc | hc
        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
          have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_162 y (by linarith) (by linarith)
          have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
          have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_465 (x + y) (by linarith) (by linarith)
          have hw5 : (1158993733/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_910 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
          have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_172 y (by linarith) (by linarith)
          have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
          have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_479 (x + y) (by linarith) (by linarith)
          have hw5 : (242372143/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_924 (x + y + z) (by linarith) (by linarith)
          linarith
    · rcases le_total x (4307/4096:ℝ) with hc | hc
      · rcases le_total y (8109/4096:ℝ) with hc | hc
        · rcases le_total z (4267/4096:ℝ) with hc | hc
          · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
            have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_162 y (by linarith) (by linarith)
            have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
            have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_449 (x + y) (by linarith) (by linarith)
            have hw5 : (1213318631/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_923 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (8609/8192:ℝ) with hc | hc
            · rcases le_total y (16213/8192:ℝ) with hc | hc
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
                have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_352 (y + z) (by linarith) (by linarith)
                have hw5 : (634442007/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_944 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
                have hw4 : (153341/5000000000000:ℝ) ≤ wfun (y + z) := wc_356 (y + z) (by linarith) (by linarith)
                have hw5 : (648175967/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_954 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
              have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_162 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
              have hw3 : (64456359/10000000000000:ℝ) ≤ wfun (x + y) := wc_458 (x + y) (by linarith) (by linarith)
              have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_353 (y + z) (by linarith) (by linarith)
              have hw5 : (647786457/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_955 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (4267/4096:ℝ) with hc | hc
          · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
            have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_172 y (by linarith) (by linarith)
            have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
            have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_465 (x + y) (by linarith) (by linarith)
            have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_353 (y + z) (by linarith) (by linarith)
            have hw5 : (1267359331/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_946 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (8609/8192:ℝ) with hc | hc
            · rcases le_total y (16223/8192:ℝ) with hc | hc
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
                have hw4 : (593183/5000000000000:ℝ) ≤ wfun (y + z) := wc_358 (y + z) (by linarith) (by linarith)
                have hw5 : (1324095821/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_964 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
                have hw4 : (2638657/10000000000000:ℝ) ≤ wfun (y + z) := wc_369 (y + z) (by linarith) (by linarith)
                have hw5 : (338028751/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_979 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
              have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_172 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
              have hw3 : (82672123/10000000000000:ℝ) ≤ wfun (x + y) := wc_472 (x + y) (by linarith) (by linarith)
              have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_359 (y + z) (by linarith) (by linarith)
              have hw5 : (1351302719/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_980 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total y (8109/4096:ℝ) with hc | hc
        · rcases le_total z (4267/4096:ℝ) with hc | hc
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
            have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_162 y (by linarith) (by linarith)
            have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
            have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_465 (x + y) (by linarith) (by linarith)
            have hw5 : (1267359331/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_946 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
            have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_162 y (by linarith) (by linarith)
            have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
            have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_465 (x + y) (by linarith) (by linarith)
            have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_353 (y + z) (by linarith) (by linarith)
            have hw5 : (52900211/400000000000:ℝ) ≤ wfun (x + y + z) := wc_966 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (4267/4096:ℝ) with hc | hc
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
            have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_172 y (by linarith) (by linarith)
            have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
            have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_479 (x + y) (by linarith) (by linarith)
            have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_353 (y + z) (by linarith) (by linarith)
            have hw5 : (52900211/400000000000:ℝ) ≤ wfun (x + y + z) := wc_966 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
            have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_172 y (by linarith) (by linarith)
            have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
            have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_479 (x + y) (by linarith) (by linarith)
            have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_359 (y + z) (by linarith) (by linarith)
            have hw5 : (275750223/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_990 (x + y + z) (by linarith) (by linarith)
            linarith
  · rcases le_total z (2131/2048:ℝ) with hc | hc
    · rcases le_total x (4307/4096:ℝ) with hc | hc
      · rcases le_total y (8119/4096:ℝ) with hc | hc
        · rcases le_total z (4257/4096:ℝ) with hc | hc
          · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
            have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_179 y (by linarith) (by linarith)
            have hw2 : (2586175977/10000000000000:ℝ) ≤ wfun z := wc_23 z (by linarith) (by linarith)
            have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_479 (x + y) (by linarith) (by linarith)
            have hw5 : (1213318631/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_923 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
            have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_179 y (by linarith) (by linarith)
            have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
            have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_479 (x + y) (by linarith) (by linarith)
            have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_353 (y + z) (by linarith) (by linarith)
            have hw5 : (1267359331/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_946 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (4257/4096:ℝ) with hc | hc
          · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
            have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
            have hw2 : (2586175977/10000000000000:ℝ) ≤ wfun z := wc_23 z (by linarith) (by linarith)
            have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_506 (x + y) (by linarith) (by linarith)
            have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_353 (y + z) (by linarith) (by linarith)
            have hw5 : (1267359331/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_946 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
            have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
            have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
            have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_506 (x + y) (by linarith) (by linarith)
            have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_359 (y + z) (by linarith) (by linarith)
            have hw5 : (52900211/400000000000:ℝ) ≤ wfun (x + y + z) := wc_966 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total y (8119/4096:ℝ) with hc | hc
        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
          have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_179 y (by linarith) (by linarith)
          have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
          have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_506 (x + y) (by linarith) (by linarith)
          have hw5 : (1265836939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_947 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
          have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
          have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
          have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_515 (x + y) (by linarith) (by linarith)
          have hw4 : (41/1250000000000:ℝ) ≤ wfun (y + z) := wc_354 (y + z) (by linarith) (by linarith)
          have hw5 : (660458559/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_967 (x + y + z) (by linarith) (by linarith)
          linarith
    · rcases le_total x (4307/4096:ℝ) with hc | hc
      · rcases le_total y (8119/4096:ℝ) with hc | hc
        · rcases le_total z (4267/4096:ℝ) with hc | hc
          · rcases le_total x (8609/8192:ℝ) with hc | hc
            · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
              have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_179 y (by linarith) (by linarith)
              have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
              have hw3 : (46310863/5000000000000:ℝ) ≤ wfun (x + y) := wc_478 (x + y) (by linarith) (by linarith)
              have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_359 (y + z) (by linarith) (by linarith)
              have hw5 : (1323300249/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_965 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
              have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_179 y (by linarith) (by linarith)
              have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
              have hw3 : (25782839/2500000000000:ℝ) ≤ wfun (x + y) := wc_499 (x + y) (by linarith) (by linarith)
              have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_359 (y + z) (by linarith) (by linarith)
              have hw5 : (1351302719/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_980 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (8609/8192:ℝ) with hc | hc
            · rcases le_total y (16233/8192:ℝ) with hc | hc
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
                have hw4 : (4662827/10000000000000:ℝ) ≤ wfun (y + z) := wc_373 (y + z) (by linarith) (by linarith)
                have hw5 : (690204403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_988 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
                have hw4 : (7258139/10000000000000:ℝ) ≤ wfun (y + z) := wc_380 (y + z) (by linarith) (by linarith)
                have hw5 : (176122069/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1000 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16233/8192:ℝ) with hc | hc
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
                have hw4 : (4662827/10000000000000:ℝ) ≤ wfun (y + z) := wc_373 (y + z) (by linarith) (by linarith)
                have hw5 : (176122069/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1000 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
                have hw4 : (7258139/10000000000000:ℝ) ≤ wfun (y + z) := wc_380 (y + z) (by linarith) (by linarith)
                have hw5 : (718908779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1009 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (4267/4096:ℝ) with hc | hc
          · rcases le_total x (8609/8192:ℝ) with hc | hc
            · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
              have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
              have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
              have hw3 : (114200161/10000000000000:ℝ) ≤ wfun (x + y) := wc_505 (x + y) (by linarith) (by linarith)
              have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_374 (y + z) (by linarith) (by linarith)
              have hw5 : (1379579649/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_989 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
              have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
              have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
              have hw3 : (15728411/1250000000000:ℝ) ≤ wfun (x + y) := wc_511 (x + y) (by linarith) (by linarith)
              have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_374 (y + z) (by linarith) (by linarith)
              have hw5 : (1408130363/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1001 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (8609/8192:ℝ) with hc | hc
            · rcases le_total y (16243/8192:ℝ) with hc | hc
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
                have hw4 : (5211923/5000000000000:ℝ) ≤ wfun (y + z) := wc_386 (y + z) (by linarith) (by linarith)
                have hw5 : (718908779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1009 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
                have hw4 : (3539799/2500000000000:ℝ) ≤ wfun (y + z) := wc_396 (y + z) (by linarith) (by linarith)
                have hw5 : (1466931139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1033 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
              have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
              have hw3 : (15728411/1250000000000:ℝ) ≤ wfun (x + y) := wc_511 (x + y) (by linarith) (by linarith)
              have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_387 (y + z) (by linarith) (by linarith)
              have hw5 : (1466050409/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1034 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total y (8119/4096:ℝ) with hc | hc
        · rcases le_total z (4267/4096:ℝ) with hc | hc
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
            have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_179 y (by linarith) (by linarith)
            have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
            have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_506 (x + y) (by linarith) (by linarith)
            have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_359 (y + z) (by linarith) (by linarith)
            have hw5 : (275750223/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_990 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (8619/8192:ℝ) with hc | hc
            · have hw0 : (25860883/1250000000000:ℝ) ≤ wfun x := wc_88 x (by linarith) (by linarith)
              have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_179 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
              have hw3 : (114200161/10000000000000:ℝ) ≤ wfun (x + y) := wc_505 (x + y) (by linarith) (by linarith)
              have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_374 (y + z) (by linarith) (by linarith)
              have hw5 : (718477089/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1010 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_90 x (by linarith) (by linarith)
              have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_179 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
              have hw3 : (15728411/1250000000000:ℝ) ≤ wfun (x + y) := wc_511 (x + y) (by linarith) (by linarith)
              have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_374 (y + z) (by linarith) (by linarith)
              have hw5 : (1466050409/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1034 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (4267/4096:ℝ) with hc | hc
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
            have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
            have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
            have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_515 (x + y) (by linarith) (by linarith)
            have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_374 (y + z) (by linarith) (by linarith)
            have hw5 : (718045723/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1011 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
            have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
            have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
            have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_515 (x + y) (by linarith) (by linarith)
            have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_387 (y + z) (by linarith) (by linarith)
            have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1044 (x + y + z) (by linarith) (by linarith)
            linarith

set_option maxHeartbeats 20000000 in
lemma ch_93 (x y z : ℝ) (hx1 : (4287/4096:ℝ) ≤ x) (hx2 : x ≤ (1073/1024:ℝ))
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
  · rcases le_total x (8579/8192:ℝ) with hc | hc
    · rcases le_total y (16213/8192:ℝ) with hc | hc
      · rcases le_total z (8569/8192:ℝ) with hc | hc
        · rcases le_total x (17153/16384:ℝ) with hc | hc
          · rcases le_total y (32421/16384:ℝ) with hc | hc
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
              have hw4 : (5218271/5000000000000:ℝ) ≤ wfun (y + z) := wc_384 (y + z) (by linarith) (by linarith)
              have hw5 : (1270410991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_941 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
              have hw4 : (2447049/2000000000000:ℝ) ≤ wfun (y + z) := wc_392 (y + z) (by linarith) (by linarith)
              have hw5 : (1284126783/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_949 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32421/16384:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
              have hw4 : (5218271/5000000000000:ℝ) ≤ wfun (y + z) := wc_384 (y + z) (by linarith) (by linarith)
              have hw5 : (1284126783/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_949 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
              have hw4 : (2447049/2000000000000:ℝ) ≤ wfun (y + z) := wc_392 (y + z) (by linarith) (by linarith)
              have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17153/16384:ℝ) with hc | hc
          · rcases le_total y (32421/16384:ℝ) with hc | hc
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
              have hw4 : (7088219/5000000000000:ℝ) ≤ wfun (y + z) := wc_394 (y + z) (by linarith) (by linarith)
              have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
              have hw4 : (650401/400000000000:ℝ) ≤ wfun (y + z) := wc_398 (y + z) (by linarith) (by linarith)
              have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32421/16384:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
              have hw4 : (7088219/5000000000000:ℝ) ≤ wfun (y + z) := wc_394 (y + z) (by linarith) (by linarith)
              have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
              have hw4 : (650401/400000000000:ℝ) ≤ wfun (y + z) := wc_398 (y + z) (by linarith) (by linarith)
              have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (8569/8192:ℝ) with hc | hc
        · rcases le_total x (17153/16384:ℝ) with hc | hc
          · rcases le_total y (32431/16384:ℝ) with hc | hc
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
              have hw4 : (7088219/5000000000000:ℝ) ≤ wfun (y + z) := wc_394 (y + z) (by linarith) (by linarith)
              have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
              have hw4 : (650401/400000000000:ℝ) ≤ wfun (y + z) := wc_398 (y + z) (by linarith) (by linarith)
              have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32431/16384:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
              have hw4 : (7088219/5000000000000:ℝ) ≤ wfun (y + z) := wc_394 (y + z) (by linarith) (by linarith)
              have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
              have hw4 : (650401/400000000000:ℝ) ≤ wfun (y + z) := wc_398 (y + z) (by linarith) (by linarith)
              have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17153/16384:ℝ) with hc | hc
          · rcases le_total y (32431/16384:ℝ) with hc | hc
            · rcases le_total z (17143/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
                have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
                have hw4 : (18493409/10000000000000:ℝ) ≤ wfun (y + z) := wc_399 (y + z) (by linarith) (by linarith)
                have hw5 : (1326087369/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_960 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
                have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
                have hw4 : (4172491/2000000000000:ℝ) ≤ wfun (y + z) := wc_405 (y + z) (by linarith) (by linarith)
                have hw5 : (1340083459/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_972 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (17143/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
                have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
                have hw4 : (4172491/2000000000000:ℝ) ≤ wfun (y + z) := wc_405 (y + z) (by linarith) (by linarith)
                have hw5 : (1340083459/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_972 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
                have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
                have hw4 : (11686831/5000000000000:ℝ) ≤ wfun (y + z) := wc_407 (y + z) (by linarith) (by linarith)
                have hw5 : (338537097/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_975 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (32431/16384:ℝ) with hc | hc
            · rcases le_total z (17143/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
                have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
                have hw4 : (18493409/10000000000000:ℝ) ≤ wfun (y + z) := wc_399 (y + z) (by linarith) (by linarith)
                have hw5 : (1340083459/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_972 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
                have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
                have hw4 : (4172491/2000000000000:ℝ) ≤ wfun (y + z) := wc_405 (y + z) (by linarith) (by linarith)
                have hw5 : (338537097/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_975 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (17143/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
                have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
                have hw4 : (4172491/2000000000000:ℝ) ≤ wfun (y + z) := wc_405 (y + z) (by linarith) (by linarith)
                have hw5 : (338537097/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_975 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
                have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
                have hw4 : (11686831/5000000000000:ℝ) ≤ wfun (y + z) := wc_407 (y + z) (by linarith) (by linarith)
                have hw5 : (171035259/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_981 (x + y + z) (by linarith) (by linarith)
                linarith
    · rcases le_total y (16213/8192:ℝ) with hc | hc
      · rcases le_total z (8569/8192:ℝ) with hc | hc
        · rcases le_total x (17163/16384:ℝ) with hc | hc
          · rcases le_total y (32421/16384:ℝ) with hc | hc
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
              have hw4 : (5218271/5000000000000:ℝ) ≤ wfun (y + z) := wc_384 (y + z) (by linarith) (by linarith)
              have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
              have hw4 : (2447049/2000000000000:ℝ) ≤ wfun (y + z) := wc_392 (y + z) (by linarith) (by linarith)
              have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32421/16384:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
              have hw4 : (5218271/5000000000000:ℝ) ≤ wfun (y + z) := wc_384 (y + z) (by linarith) (by linarith)
              have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
              have hw4 : (2447049/2000000000000:ℝ) ≤ wfun (y + z) := wc_392 (y + z) (by linarith) (by linarith)
              have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17163/16384:ℝ) with hc | hc
          · rcases le_total y (32421/16384:ℝ) with hc | hc
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
              have hw4 : (7088219/5000000000000:ℝ) ≤ wfun (y + z) := wc_394 (y + z) (by linarith) (by linarith)
              have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
              have hw4 : (650401/400000000000:ℝ) ≤ wfun (y + z) := wc_398 (y + z) (by linarith) (by linarith)
              have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32421/16384:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
              have hw4 : (7088219/5000000000000:ℝ) ≤ wfun (y + z) := wc_394 (y + z) (by linarith) (by linarith)
              have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
              have hw4 : (650401/400000000000:ℝ) ≤ wfun (y + z) := wc_398 (y + z) (by linarith) (by linarith)
              have hw5 : (676870703/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_976 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (8569/8192:ℝ) with hc | hc
        · rcases le_total x (17163/16384:ℝ) with hc | hc
          · rcases le_total y (32431/16384:ℝ) with hc | hc
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
              have hw4 : (7088219/5000000000000:ℝ) ≤ wfun (y + z) := wc_394 (y + z) (by linarith) (by linarith)
              have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
              have hw4 : (650401/400000000000:ℝ) ≤ wfun (y + z) := wc_398 (y + z) (by linarith) (by linarith)
              have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32431/16384:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
              have hw4 : (7088219/5000000000000:ℝ) ≤ wfun (y + z) := wc_394 (y + z) (by linarith) (by linarith)
              have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
              have hw4 : (650401/400000000000:ℝ) ≤ wfun (y + z) := wc_398 (y + z) (by linarith) (by linarith)
              have hw5 : (676870703/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_976 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17163/16384:ℝ) with hc | hc
          · rcases le_total y (32431/16384:ℝ) with hc | hc
            · rcases le_total z (17143/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
                have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
                have hw4 : (18493409/10000000000000:ℝ) ≤ wfun (y + z) := wc_399 (y + z) (by linarith) (by linarith)
                have hw5 : (338537097/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_975 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
                have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
                have hw4 : (4172491/2000000000000:ℝ) ≤ wfun (y + z) := wc_405 (y + z) (by linarith) (by linarith)
                have hw5 : (171035259/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_981 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (17143/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
                have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
                have hw4 : (4172491/2000000000000:ℝ) ≤ wfun (y + z) := wc_405 (y + z) (by linarith) (by linarith)
                have hw5 : (171035259/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_981 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
                have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
                have hw4 : (11686831/5000000000000:ℝ) ≤ wfun (y + z) := wc_407 (y + z) (by linarith) (by linarith)
                have hw5 : (1382484427/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_984 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (32431/16384:ℝ) with hc | hc
            · rcases le_total z (17143/16384:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
                have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
                have hw4 : (18493409/10000000000000:ℝ) ≤ wfun (y + z) := wc_399 (y + z) (by linarith) (by linarith)
                have hw5 : (171035259/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_981 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
                have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
                have hw4 : (4172491/2000000000000:ℝ) ≤ wfun (y + z) := wc_405 (y + z) (by linarith) (by linarith)
                have hw5 : (1382484427/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_984 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (17143/16384:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
                have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
                have hw4 : (4172491/2000000000000:ℝ) ≤ wfun (y + z) := wc_405 (y + z) (by linarith) (by linarith)
                have hw5 : (1382484427/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_984 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
                have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
                have hw4 : (11686831/5000000000000:ℝ) ≤ wfun (y + z) := wc_407 (y + z) (by linarith) (by linarith)
                have hw5 : (174594421/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_993 (x + y + z) (by linarith) (by linarith)
                linarith
  · rcases le_total x (8579/8192:ℝ) with hc | hc
    · rcases le_total y (16213/8192:ℝ) with hc | hc
      · rcases le_total z (8579/8192:ℝ) with hc | hc
        · rcases le_total x (17153/16384:ℝ) with hc | hc
          · rcases le_total y (32421/16384:ℝ) with hc | hc
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
              have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
              have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (17153/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
                have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
                have hw4 : (4172491/2000000000000:ℝ) ≤ wfun (y + z) := wc_405 (y + z) (by linarith) (by linarith)
                have hw5 : (1340083459/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_972 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
                have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
                have hw4 : (11686831/5000000000000:ℝ) ≤ wfun (y + z) := wc_407 (y + z) (by linarith) (by linarith)
                have hw5 : (338537097/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_975 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (32421/16384:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
              have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
              have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (17153/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
                have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
                have hw4 : (4172491/2000000000000:ℝ) ≤ wfun (y + z) := wc_405 (y + z) (by linarith) (by linarith)
                have hw5 : (338537097/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_975 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
                have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
                have hw4 : (11686831/5000000000000:ℝ) ≤ wfun (y + z) := wc_407 (y + z) (by linarith) (by linarith)
                have hw5 : (171035259/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_981 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (17153/16384:ℝ) with hc | hc
          · rcases le_total y (32421/16384:ℝ) with hc | hc
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
              have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
              have hw5 : (676870703/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_976 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
              have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
              have hw5 : (170983859/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_982 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32421/16384:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
              have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
              have hw5 : (170983859/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_982 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (17163/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
                have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
                have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
                have hw4 : (13013467/5000000000000:ℝ) ≤ wfun (y + z) := wc_411 (y + z) (by linarith) (by linarith)
                have hw5 : (1382484427/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_984 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
                have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
                have hw4 : (28822173/10000000000000:ℝ) ≤ wfun (y + z) := wc_413 (y + z) (by linarith) (by linarith)
                have hw5 : (174594421/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_993 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total z (8579/8192:ℝ) with hc | hc
        · rcases le_total x (17153/16384:ℝ) with hc | hc
          · rcases le_total y (32431/16384:ℝ) with hc | hc
            · rcases le_total z (17153/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
                have hw4 : (11686831/5000000000000:ℝ) ≤ wfun (y + z) := wc_407 (y + z) (by linarith) (by linarith)
                have hw5 : (338537097/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_975 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
                have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
                have hw4 : (13013467/5000000000000:ℝ) ≤ wfun (y + z) := wc_411 (y + z) (by linarith) (by linarith)
                have hw5 : (171035259/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_981 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (17153/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
                have hw4 : (13013467/5000000000000:ℝ) ≤ wfun (y + z) := wc_411 (y + z) (by linarith) (by linarith)
                have hw5 : (171035259/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_981 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
                have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
                have hw4 : (28822173/10000000000000:ℝ) ≤ wfun (y + z) := wc_413 (y + z) (by linarith) (by linarith)
                have hw5 : (1382484427/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_984 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (32431/16384:ℝ) with hc | hc
            · rcases le_total z (17153/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
                have hw4 : (11686831/5000000000000:ℝ) ≤ wfun (y + z) := wc_407 (y + z) (by linarith) (by linarith)
                have hw5 : (171035259/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_981 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
                have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
                have hw4 : (13013467/5000000000000:ℝ) ≤ wfun (y + z) := wc_411 (y + z) (by linarith) (by linarith)
                have hw5 : (1382484427/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_984 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (17153/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
                have hw4 : (13013467/5000000000000:ℝ) ≤ wfun (y + z) := wc_411 (y + z) (by linarith) (by linarith)
                have hw5 : (1382484427/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_984 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
                have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
                have hw4 : (28822173/10000000000000:ℝ) ≤ wfun (y + z) := wc_413 (y + z) (by linarith) (by linarith)
                have hw5 : (174594421/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_993 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (17153/16384:ℝ) with hc | hc
          · rcases le_total y (32431/16384:ℝ) with hc | hc
            · rcases le_total z (17163/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
                have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
                have hw4 : (28822173/10000000000000:ℝ) ≤ wfun (y + z) := wc_413 (y + z) (by linarith) (by linarith)
                have hw5 : (1382484427/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_984 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
                have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
                have hw4 : (396991/125000000000:ℝ) ≤ wfun (y + z) := wc_423 (y + z) (by linarith) (by linarith)
                have hw5 : (174594421/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_993 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (17163/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
                have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
                have hw4 : (396991/125000000000:ℝ) ≤ wfun (y + z) := wc_423 (y + z) (by linarith) (by linarith)
                have hw5 : (174594421/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_993 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
                have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
                have hw4 : (8709539/2500000000000:ℝ) ≤ wfun (y + z) := wc_425 (y + z) (by linarith) (by linarith)
                have hw5 : (1411094809/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_996 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (32431/16384:ℝ) with hc | hc
            · rcases le_total z (17163/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
                have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
                have hw4 : (28822173/10000000000000:ℝ) ≤ wfun (y + z) := wc_413 (y + z) (by linarith) (by linarith)
                have hw5 : (174594421/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_993 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
                have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
                have hw4 : (396991/125000000000:ℝ) ≤ wfun (y + z) := wc_423 (y + z) (by linarith) (by linarith)
                have hw5 : (1411094809/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_996 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (17163/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
                have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
                have hw4 : (396991/125000000000:ℝ) ≤ wfun (y + z) := wc_423 (y + z) (by linarith) (by linarith)
                have hw5 : (1411094809/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_996 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
                have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
                have hw4 : (8709539/2500000000000:ℝ) ≤ wfun (y + z) := wc_425 (y + z) (by linarith) (by linarith)
                have hw5 : (285100533/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1002 (x + y + z) (by linarith) (by linarith)
                linarith
    · rcases le_total y (16213/8192:ℝ) with hc | hc
      · rcases le_total z (8579/8192:ℝ) with hc | hc
        · rcases le_total x (17163/16384:ℝ) with hc | hc
          · rcases le_total y (32421/16384:ℝ) with hc | hc
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
              have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
              have hw5 : (676870703/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_976 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (17153/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
                have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
                have hw4 : (4172491/2000000000000:ℝ) ≤ wfun (y + z) := wc_405 (y + z) (by linarith) (by linarith)
                have hw5 : (171035259/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_981 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
                have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
                have hw4 : (11686831/5000000000000:ℝ) ≤ wfun (y + z) := wc_407 (y + z) (by linarith) (by linarith)
                have hw5 : (1382484427/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_984 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (32421/16384:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
              have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
              have hw5 : (170983859/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_982 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
              have hw4 : (10426997/5000000000000:ℝ) ≤ wfun (y + z) := wc_406 (y + z) (by linarith) (by linarith)
              have hw5 : (1382068991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_985 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17163/16384:ℝ) with hc | hc
          · rcases le_total y (32421/16384:ℝ) with hc | hc
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
              have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
              have hw5 : (1382068991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_985 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
              have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
              have hw5 : (55853427/400000000000:ℝ) ≤ wfun (x + y + z) := wc_994 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32421/16384:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
              have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
              have hw5 : (55853427/400000000000:ℝ) ≤ wfun (x + y + z) := wc_994 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
              have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
              have hw5 : (1410670839/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_997 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (8579/8192:ℝ) with hc | hc
        · rcases le_total x (17163/16384:ℝ) with hc | hc
          · rcases le_total y (32431/16384:ℝ) with hc | hc
            · rcases le_total z (17153/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
                have hw4 : (11686831/5000000000000:ℝ) ≤ wfun (y + z) := wc_407 (y + z) (by linarith) (by linarith)
                have hw5 : (1382484427/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_984 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
                have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
                have hw4 : (13013467/5000000000000:ℝ) ≤ wfun (y + z) := wc_411 (y + z) (by linarith) (by linarith)
                have hw5 : (174594421/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_993 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (17153/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
                have hw4 : (13013467/5000000000000:ℝ) ≤ wfun (y + z) := wc_411 (y + z) (by linarith) (by linarith)
                have hw5 : (174594421/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_993 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
                have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
                have hw4 : (28822173/10000000000000:ℝ) ≤ wfun (y + z) := wc_413 (y + z) (by linarith) (by linarith)
                have hw5 : (1411094809/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_996 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (32431/16384:ℝ) with hc | hc
            · rcases le_total z (17153/16384:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
                have hw4 : (11686831/5000000000000:ℝ) ≤ wfun (y + z) := wc_407 (y + z) (by linarith) (by linarith)
                have hw5 : (174594421/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_993 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
                have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
                have hw4 : (13013467/5000000000000:ℝ) ≤ wfun (y + z) := wc_411 (y + z) (by linarith) (by linarith)
                have hw5 : (1411094809/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_996 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (17153/16384:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
                have hw4 : (13013467/5000000000000:ℝ) ≤ wfun (y + z) := wc_411 (y + z) (by linarith) (by linarith)
                have hw5 : (1411094809/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_996 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
                have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
                have hw4 : (28822173/10000000000000:ℝ) ≤ wfun (y + z) := wc_413 (y + z) (by linarith) (by linarith)
                have hw5 : (285100533/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1002 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (17163/16384:ℝ) with hc | hc
          · rcases le_total y (32431/16384:ℝ) with hc | hc
            · rcases le_total z (17163/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
                have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
                have hw4 : (28822173/10000000000000:ℝ) ≤ wfun (y + z) := wc_413 (y + z) (by linarith) (by linarith)
                have hw5 : (1411094809/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_996 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
                have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
                have hw4 : (396991/125000000000:ℝ) ≤ wfun (y + z) := wc_423 (y + z) (by linarith) (by linarith)
                have hw5 : (285100533/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1002 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (17163/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
                have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
                have hw4 : (396991/125000000000:ℝ) ≤ wfun (y + z) := wc_423 (y + z) (by linarith) (by linarith)
                have hw5 : (285100533/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1002 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
                have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
                have hw4 : (8709539/2500000000000:ℝ) ≤ wfun (y + z) := wc_425 (y + z) (by linarith) (by linarith)
                have hw5 : (1439978849/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1005 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (32431/16384:ℝ) with hc | hc
            · rcases le_total z (17163/16384:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
                have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
                have hw4 : (28822173/10000000000000:ℝ) ≤ wfun (y + z) := wc_413 (y + z) (by linarith) (by linarith)
                have hw5 : (285100533/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1002 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
                have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
                have hw4 : (396991/125000000000:ℝ) ≤ wfun (y + z) := wc_423 (y + z) (by linarith) (by linarith)
                have hw5 : (1439978849/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1005 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (17163/16384:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
                have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
                have hw4 : (396991/125000000000:ℝ) ≤ wfun (y + z) := wc_423 (y + z) (by linarith) (by linarith)
                have hw5 : (1439978849/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1005 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
                have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
                have hw4 : (8709539/2500000000000:ℝ) ≤ wfun (y + z) := wc_425 (y + z) (by linarith) (by linarith)
                have hw5 : (363630819/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1026 (x + y + z) (by linarith) (by linarith)
                linarith

set_option maxHeartbeats 20000000 in
lemma ch_106 (x y z : ℝ) (hx1 : (4287/4096:ℝ) ≤ x) (hx2 : x ≤ (1073/1024:ℝ))
    (hy1 : (8119/4096:ℝ) ≤ y) (hy2 : y ≤ (2031/1024:ℝ))
    (hz1 : (2141/2048:ℝ) ≤ z) (hz2 : z ≤ (1073/1024:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total z (4287/4096:ℝ) with hc | hc
  · rcases le_total x (8579/8192:ℝ) with hc | hc
    · rcases le_total y (16243/8192:ℝ) with hc | hc
      · rcases le_total z (8569/8192:ℝ) with hc | hc
        · rcases le_total x (17153/16384:ℝ) with hc | hc
          · rcases le_total y (32481/16384:ℝ) with hc | hc
            · rcases le_total z (17133/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
                have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
                have hw4 : (41420821/10000000000000:ℝ) ≤ wfun (y + z) := wc_431 (y + z) (by linarith) (by linarith)
                have hw5 : (1439978849/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1005 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
                have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
                have hw4 : (4492441/1000000000000:ℝ) ≤ wfun (y + z) := wc_437 (y + z) (by linarith) (by linarith)
                have hw5 : (363630819/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1026 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (17133/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (4492441/1000000000000:ℝ) ≤ wfun (y + z) := wc_437 (y + z) (by linarith) (by linarith)
                have hw5 : (363630819/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1026 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (6071171/1250000000000:ℝ) ≤ wfun (y + z) := wc_439 (y + z) (by linarith) (by linarith)
                have hw5 : (73456793/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1029 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (32481/16384:ℝ) with hc | hc
            · rcases le_total z (17133/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (41420821/10000000000000:ℝ) ≤ wfun (y + z) := wc_431 (y + z) (by linarith) (by linarith)
                have hw5 : (363630819/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1026 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (4492441/1000000000000:ℝ) ≤ wfun (y + z) := wc_437 (y + z) (by linarith) (by linarith)
                have hw5 : (73456793/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1029 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (17133/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (4492441/1000000000000:ℝ) ≤ wfun (y + z) := wc_437 (y + z) (by linarith) (by linarith)
                have hw5 : (73456793/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1029 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (6071171/1250000000000:ℝ) ≤ wfun (y + z) := wc_439 (y + z) (by linarith) (by linarith)
                have hw5 : (296763303/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1035 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (17153/16384:ℝ) with hc | hc
          · rcases le_total y (32481/16384:ℝ) with hc | hc
            · rcases le_total z (17143/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
                have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
                have hw4 : (6071171/1250000000000:ℝ) ≤ wfun (y + z) := wc_439 (y + z) (by linarith) (by linarith)
                have hw5 : (73456793/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1029 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
                have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
                have hw4 : (26177797/5000000000000:ℝ) ≤ wfun (y + z) := wc_443 (y + z) (by linarith) (by linarith)
                have hw5 : (296763303/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1035 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (17143/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (26177797/5000000000000:ℝ) ≤ wfun (y + z) := wc_443 (y + z) (by linarith) (by linarith)
                have hw5 : (296763303/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1035 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (14070747/2500000000000:ℝ) ≤ wfun (y + z) := wc_445 (y + z) (by linarith) (by linarith)
                have hw5 : (1498565153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1038 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (32481/16384:ℝ) with hc | hc
            · rcases le_total z (17143/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (6071171/1250000000000:ℝ) ≤ wfun (y + z) := wc_439 (y + z) (by linarith) (by linarith)
                have hw5 : (296763303/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1035 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (26177797/5000000000000:ℝ) ≤ wfun (y + z) := wc_443 (y + z) (by linarith) (by linarith)
                have hw5 : (1498565153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1038 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (17143/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (26177797/5000000000000:ℝ) ≤ wfun (y + z) := wc_443 (y + z) (by linarith) (by linarith)
                have hw5 : (1498565153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1038 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (14070747/2500000000000:ℝ) ≤ wfun (y + z) := wc_445 (y + z) (by linarith) (by linarith)
                have hw5 : (189172711/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1047 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total z (8569/8192:ℝ) with hc | hc
        · rcases le_total x (17153/16384:ℝ) with hc | hc
          · rcases le_total y (32491/16384:ℝ) with hc | hc
            · rcases le_total z (17133/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
                have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (6071171/1250000000000:ℝ) ≤ wfun (y + z) := wc_439 (y + z) (by linarith) (by linarith)
                have hw5 : (73456793/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1029 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (26177797/5000000000000:ℝ) ≤ wfun (y + z) := wc_443 (y + z) (by linarith) (by linarith)
                have hw5 : (296763303/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1035 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (17133/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
                have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
                have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                have hw4 : (26177797/5000000000000:ℝ) ≤ wfun (y + z) := wc_443 (y + z) (by linarith) (by linarith)
                have hw5 : (296763303/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1035 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
                have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                have hw4 : (14070747/2500000000000:ℝ) ≤ wfun (y + z) := wc_445 (y + z) (by linarith) (by linarith)
                have hw5 : (1498565153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1038 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (32491/16384:ℝ) with hc | hc
            · rcases le_total z (17133/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
                have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
                have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                have hw4 : (6071171/1250000000000:ℝ) ≤ wfun (y + z) := wc_439 (y + z) (by linarith) (by linarith)
                have hw5 : (296763303/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1035 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
                have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                have hw4 : (26177797/5000000000000:ℝ) ≤ wfun (y + z) := wc_443 (y + z) (by linarith) (by linarith)
                have hw5 : (1498565153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1038 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (17133/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
                have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
                have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
                have hw4 : (26177797/5000000000000:ℝ) ≤ wfun (y + z) := wc_443 (y + z) (by linarith) (by linarith)
                have hw5 : (1498565153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1038 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
                have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
                have hw4 : (14070747/2500000000000:ℝ) ≤ wfun (y + z) := wc_445 (y + z) (by linarith) (by linarith)
                have hw5 : (189172711/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1047 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (17153/16384:ℝ) with hc | hc
          · rcases le_total y (32491/16384:ℝ) with hc | hc
            · rcases le_total z (17143/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
                have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (14070747/2500000000000:ℝ) ≤ wfun (y + z) := wc_445 (y + z) (by linarith) (by linarith)
                have hw5 : (1498565153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1038 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (60351447/10000000000000:ℝ) ≤ wfun (y + z) := wc_453 (y + z) (by linarith) (by linarith)
                have hw5 : (189172711/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1047 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (17143/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
                have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
                have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                have hw4 : (60351447/10000000000000:ℝ) ≤ wfun (y + z) := wc_453 (y + z) (by linarith) (by linarith)
                have hw5 : (189172711/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1047 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
                have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                have hw4 : (16140217/2500000000000:ℝ) ≤ wfun (y + z) := wc_455 (y + z) (by linarith) (by linarith)
                have hw5 : (1528266033/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1050 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (32491/16384:ℝ) with hc | hc
            · rcases le_total z (17143/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
                have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
                have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                have hw4 : (14070747/2500000000000:ℝ) ≤ wfun (y + z) := wc_445 (y + z) (by linarith) (by linarith)
                have hw5 : (189172711/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1047 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
                have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                have hw4 : (60351447/10000000000000:ℝ) ≤ wfun (y + z) := wc_453 (y + z) (by linarith) (by linarith)
                have hw5 : (1528266033/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1050 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (17143/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
                have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
                have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
                have hw4 : (60351447/10000000000000:ℝ) ≤ wfun (y + z) := wc_453 (y + z) (by linarith) (by linarith)
                have hw5 : (1528266033/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1050 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
                have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
                have hw4 : (16140217/2500000000000:ℝ) ≤ wfun (y + z) := wc_455 (y + z) (by linarith) (by linarith)
                have hw5 : (15432181/100000000000:ℝ) ≤ wfun (x + y + z) := wc_1056 (x + y + z) (by linarith) (by linarith)
                linarith
    · rcases le_total y (16243/8192:ℝ) with hc | hc
      · rcases le_total z (8569/8192:ℝ) with hc | hc
        · rcases le_total x (17163/16384:ℝ) with hc | hc
          · rcases le_total y (32481/16384:ℝ) with hc | hc
            · rcases le_total z (17133/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (41420821/10000000000000:ℝ) ≤ wfun (y + z) := wc_431 (y + z) (by linarith) (by linarith)
                have hw5 : (73456793/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1029 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (4492441/1000000000000:ℝ) ≤ wfun (y + z) := wc_437 (y + z) (by linarith) (by linarith)
                have hw5 : (296763303/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1035 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (17133/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
                have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                have hw4 : (4492441/1000000000000:ℝ) ≤ wfun (y + z) := wc_437 (y + z) (by linarith) (by linarith)
                have hw5 : (296763303/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1035 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
                have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                have hw4 : (6071171/1250000000000:ℝ) ≤ wfun (y + z) := wc_439 (y + z) (by linarith) (by linarith)
                have hw5 : (1498565153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1038 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (32481/16384:ℝ) with hc | hc
            · rcases le_total z (17133/16384:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
                have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                have hw4 : (41420821/10000000000000:ℝ) ≤ wfun (y + z) := wc_431 (y + z) (by linarith) (by linarith)
                have hw5 : (296763303/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1035 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
                have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                have hw4 : (4492441/1000000000000:ℝ) ≤ wfun (y + z) := wc_437 (y + z) (by linarith) (by linarith)
                have hw5 : (1498565153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1038 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (17133/16384:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
                have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
                have hw4 : (4492441/1000000000000:ℝ) ≤ wfun (y + z) := wc_437 (y + z) (by linarith) (by linarith)
                have hw5 : (1498565153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1038 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
                have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
                have hw4 : (6071171/1250000000000:ℝ) ≤ wfun (y + z) := wc_439 (y + z) (by linarith) (by linarith)
                have hw5 : (189172711/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1047 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (17163/16384:ℝ) with hc | hc
          · rcases le_total y (32481/16384:ℝ) with hc | hc
            · rcases le_total z (17143/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (6071171/1250000000000:ℝ) ≤ wfun (y + z) := wc_439 (y + z) (by linarith) (by linarith)
                have hw5 : (1498565153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1038 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (26177797/5000000000000:ℝ) ≤ wfun (y + z) := wc_443 (y + z) (by linarith) (by linarith)
                have hw5 : (189172711/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1047 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (17143/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
                have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                have hw4 : (26177797/5000000000000:ℝ) ≤ wfun (y + z) := wc_443 (y + z) (by linarith) (by linarith)
                have hw5 : (189172711/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1047 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
                have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                have hw4 : (14070747/2500000000000:ℝ) ≤ wfun (y + z) := wc_445 (y + z) (by linarith) (by linarith)
                have hw5 : (1528266033/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1050 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (32481/16384:ℝ) with hc | hc
            · rcases le_total z (17143/16384:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
                have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                have hw4 : (6071171/1250000000000:ℝ) ≤ wfun (y + z) := wc_439 (y + z) (by linarith) (by linarith)
                have hw5 : (189172711/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1047 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
                have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                have hw4 : (26177797/5000000000000:ℝ) ≤ wfun (y + z) := wc_443 (y + z) (by linarith) (by linarith)
                have hw5 : (1528266033/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1050 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (17143/16384:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
                have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
                have hw4 : (26177797/5000000000000:ℝ) ≤ wfun (y + z) := wc_443 (y + z) (by linarith) (by linarith)
                have hw5 : (1528266033/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1050 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
                have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
                have hw4 : (14070747/2500000000000:ℝ) ≤ wfun (y + z) := wc_445 (y + z) (by linarith) (by linarith)
                have hw5 : (15432181/100000000000:ℝ) ≤ wfun (x + y + z) := wc_1056 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total z (8569/8192:ℝ) with hc | hc
        · rcases le_total x (17163/16384:ℝ) with hc | hc
          · rcases le_total y (32491/16384:ℝ) with hc | hc
            · rcases le_total z (17133/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
                have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
                have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
                have hw4 : (6071171/1250000000000:ℝ) ≤ wfun (y + z) := wc_439 (y + z) (by linarith) (by linarith)
                have hw5 : (1498565153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1038 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
                have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
                have hw4 : (26177797/5000000000000:ℝ) ≤ wfun (y + z) := wc_443 (y + z) (by linarith) (by linarith)
                have hw5 : (189172711/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1047 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
              have hw4 : (3270899/625000000000:ℝ) ≤ wfun (y + z) := wc_444 (y + z) (by linarith) (by linarith)
              have hw5 : (60517089/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1048 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32491/16384:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
              have hw4 : (48549689/10000000000000:ℝ) ≤ wfun (y + z) := wc_440 (y + z) (by linarith) (by linarith)
              have hw5 : (60517089/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1048 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (82806113/10000000000000:ℝ) ≤ wfun (x + y) := wc_469 (x + y) (by linarith) (by linarith)
              have hw4 : (3270899/625000000000:ℝ) ≤ wfun (y + z) := wc_444 (y + z) (by linarith) (by linarith)
              have hw5 : (305561427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1051 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17163/16384:ℝ) with hc | hc
          · rcases le_total y (32491/16384:ℝ) with hc | hc
            · rcases le_total z (17143/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
                have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
                have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
                have hw4 : (14070747/2500000000000:ℝ) ≤ wfun (y + z) := wc_445 (y + z) (by linarith) (by linarith)
                have hw5 : (1528266033/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1050 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
                have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
                have hw4 : (60351447/10000000000000:ℝ) ≤ wfun (y + z) := wc_453 (y + z) (by linarith) (by linarith)
                have hw5 : (15432181/100000000000:ℝ) ≤ wfun (x + y + z) := wc_1056 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (17143/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
                have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
                have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
                have hw4 : (60351447/10000000000000:ℝ) ≤ wfun (y + z) := wc_453 (y + z) (by linarith) (by linarith)
                have hw5 : (15432181/100000000000:ℝ) ≤ wfun (x + y + z) := wc_1056 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
                have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
                have hw4 : (16140217/2500000000000:ℝ) ≤ wfun (y + z) := wc_455 (y + z) (by linarith) (by linarith)
                have hw5 : (7791189/50000000000:ℝ) ≤ wfun (x + y + z) := wc_1059 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (32491/16384:ℝ) with hc | hc
            · rcases le_total z (17143/16384:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
                have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
                have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
                have hw4 : (14070747/2500000000000:ℝ) ≤ wfun (y + z) := wc_445 (y + z) (by linarith) (by linarith)
                have hw5 : (15432181/100000000000:ℝ) ≤ wfun (x + y + z) := wc_1056 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
                have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
                have hw4 : (60351447/10000000000000:ℝ) ≤ wfun (y + z) := wc_453 (y + z) (by linarith) (by linarith)
                have hw5 : (7791189/50000000000:ℝ) ≤ wfun (x + y + z) := wc_1059 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (82806113/10000000000000:ℝ) ≤ wfun (x + y) := wc_469 (x + y) (by linarith) (by linarith)
              have hw4 : (30163501/5000000000000:ℝ) ≤ wfun (y + z) := wc_454 (y + z) (by linarith) (by linarith)
              have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
              linarith
  · rcases le_total x (8579/8192:ℝ) with hc | hc
    · rcases le_total y (16243/8192:ℝ) with hc | hc
      · rcases le_total z (8579/8192:ℝ) with hc | hc
        · rcases le_total x (17153/16384:ℝ) with hc | hc
          · rcases le_total y (32481/16384:ℝ) with hc | hc
            · rcases le_total z (17153/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
                have hw4 : (14070747/2500000000000:ℝ) ≤ wfun (y + z) := wc_445 (y + z) (by linarith) (by linarith)
                have hw5 : (1498565153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1038 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
                have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
                have hw4 : (60351447/10000000000000:ℝ) ≤ wfun (y + z) := wc_453 (y + z) (by linarith) (by linarith)
                have hw5 : (189172711/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1047 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (17153/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (60351447/10000000000000:ℝ) ≤ wfun (y + z) := wc_453 (y + z) (by linarith) (by linarith)
                have hw5 : (189172711/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1047 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (16140217/2500000000000:ℝ) ≤ wfun (y + z) := wc_455 (y + z) (by linarith) (by linarith)
                have hw5 : (1528266033/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1050 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (32481/16384:ℝ) with hc | hc
            · rcases le_total z (17153/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (14070747/2500000000000:ℝ) ≤ wfun (y + z) := wc_445 (y + z) (by linarith) (by linarith)
                have hw5 : (189172711/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1047 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (60351447/10000000000000:ℝ) ≤ wfun (y + z) := wc_453 (y + z) (by linarith) (by linarith)
                have hw5 : (1528266033/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1050 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (17153/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (60351447/10000000000000:ℝ) ≤ wfun (y + z) := wc_453 (y + z) (by linarith) (by linarith)
                have hw5 : (1528266033/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1050 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (16140217/2500000000000:ℝ) ≤ wfun (y + z) := wc_455 (y + z) (by linarith) (by linarith)
                have hw5 : (15432181/100000000000:ℝ) ≤ wfun (x + y + z) := wc_1056 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (17153/16384:ℝ) with hc | hc
          · rcases le_total y (32481/16384:ℝ) with hc | hc
            · rcases le_total z (17163/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
                have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
                have hw4 : (16140217/2500000000000:ℝ) ≤ wfun (y + z) := wc_455 (y + z) (by linarith) (by linarith)
                have hw5 : (1528266033/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1050 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
                have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
                have hw4 : (68911149/10000000000000:ℝ) ≤ wfun (y + z) := wc_459 (y + z) (by linarith) (by linarith)
                have hw5 : (15432181/100000000000:ℝ) ≤ wfun (x + y + z) := wc_1056 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (17163/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (68911149/10000000000000:ℝ) ≤ wfun (y + z) := wc_459 (y + z) (by linarith) (by linarith)
                have hw5 : (15432181/100000000000:ℝ) ≤ wfun (x + y + z) := wc_1056 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (73402187/10000000000000:ℝ) ≤ wfun (y + z) := wc_461 (y + z) (by linarith) (by linarith)
                have hw5 : (7791189/50000000000:ℝ) ≤ wfun (x + y + z) := wc_1059 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (32481/16384:ℝ) with hc | hc
            · rcases le_total z (17163/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (16140217/2500000000000:ℝ) ≤ wfun (y + z) := wc_455 (y + z) (by linarith) (by linarith)
                have hw5 : (15432181/100000000000:ℝ) ≤ wfun (x + y + z) := wc_1056 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (68911149/10000000000000:ℝ) ≤ wfun (y + z) := wc_459 (y + z) (by linarith) (by linarith)
                have hw5 : (7791189/50000000000:ℝ) ≤ wfun (x + y + z) := wc_1059 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (17163/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (68911149/10000000000000:ℝ) ≤ wfun (y + z) := wc_459 (y + z) (by linarith) (by linarith)
                have hw5 : (7791189/50000000000:ℝ) ≤ wfun (x + y + z) := wc_1059 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (73402187/10000000000000:ℝ) ≤ wfun (y + z) := wc_461 (y + z) (by linarith) (by linarith)
                have hw5 : (31466501/200000000000:ℝ) ≤ wfun (x + y + z) := wc_1071 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total z (8579/8192:ℝ) with hc | hc
        · rcases le_total x (17153/16384:ℝ) with hc | hc
          · rcases le_total y (32491/16384:ℝ) with hc | hc
            · rcases le_total z (17153/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
                have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (16140217/2500000000000:ℝ) ≤ wfun (y + z) := wc_455 (y + z) (by linarith) (by linarith)
                have hw5 : (1528266033/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1050 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (68911149/10000000000000:ℝ) ≤ wfun (y + z) := wc_459 (y + z) (by linarith) (by linarith)
                have hw5 : (15432181/100000000000:ℝ) ≤ wfun (x + y + z) := wc_1056 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (17153/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
                have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                have hw4 : (68911149/10000000000000:ℝ) ≤ wfun (y + z) := wc_459 (y + z) (by linarith) (by linarith)
                have hw5 : (15432181/100000000000:ℝ) ≤ wfun (x + y + z) := wc_1056 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
                have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                have hw4 : (73402187/10000000000000:ℝ) ≤ wfun (y + z) := wc_461 (y + z) (by linarith) (by linarith)
                have hw5 : (7791189/50000000000:ℝ) ≤ wfun (x + y + z) := wc_1059 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (32491/16384:ℝ) with hc | hc
            · rcases le_total z (17153/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
                have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                have hw4 : (16140217/2500000000000:ℝ) ≤ wfun (y + z) := wc_455 (y + z) (by linarith) (by linarith)
                have hw5 : (15432181/100000000000:ℝ) ≤ wfun (x + y + z) := wc_1056 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
                have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                have hw4 : (68911149/10000000000000:ℝ) ≤ wfun (y + z) := wc_459 (y + z) (by linarith) (by linarith)
                have hw5 : (7791189/50000000000:ℝ) ≤ wfun (x + y + z) := wc_1059 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (17153/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
                have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
                have hw4 : (68911149/10000000000000:ℝ) ≤ wfun (y + z) := wc_459 (y + z) (by linarith) (by linarith)
                have hw5 : (7791189/50000000000:ℝ) ≤ wfun (x + y + z) := wc_1059 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
                have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
                have hw4 : (73402187/10000000000000:ℝ) ≤ wfun (y + z) := wc_461 (y + z) (by linarith) (by linarith)
                have hw5 : (31466501/200000000000:ℝ) ≤ wfun (x + y + z) := wc_1071 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (17153/16384:ℝ) with hc | hc
          · rcases le_total y (32491/16384:ℝ) with hc | hc
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
              have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
              have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
              have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
              have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32491/16384:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
              have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
              have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
              have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
              have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total y (16243/8192:ℝ) with hc | hc
      · rcases le_total z (8579/8192:ℝ) with hc | hc
        · rcases le_total x (17163/16384:ℝ) with hc | hc
          · rcases le_total y (32481/16384:ℝ) with hc | hc
            · rcases le_total z (17153/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (14070747/2500000000000:ℝ) ≤ wfun (y + z) := wc_445 (y + z) (by linarith) (by linarith)
                have hw5 : (1528266033/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1050 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (60351447/10000000000000:ℝ) ≤ wfun (y + z) := wc_453 (y + z) (by linarith) (by linarith)
                have hw5 : (15432181/100000000000:ℝ) ≤ wfun (x + y + z) := wc_1056 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (17153/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                have hw4 : (60351447/10000000000000:ℝ) ≤ wfun (y + z) := wc_453 (y + z) (by linarith) (by linarith)
                have hw5 : (15432181/100000000000:ℝ) ≤ wfun (x + y + z) := wc_1056 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
                have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                have hw4 : (16140217/2500000000000:ℝ) ≤ wfun (y + z) := wc_455 (y + z) (by linarith) (by linarith)
                have hw5 : (7791189/50000000000:ℝ) ≤ wfun (x + y + z) := wc_1059 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (32481/16384:ℝ) with hc | hc
            · rcases le_total z (17153/16384:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                have hw4 : (14070747/2500000000000:ℝ) ≤ wfun (y + z) := wc_445 (y + z) (by linarith) (by linarith)
                have hw5 : (15432181/100000000000:ℝ) ≤ wfun (x + y + z) := wc_1056 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
                have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                have hw4 : (60351447/10000000000000:ℝ) ≤ wfun (y + z) := wc_453 (y + z) (by linarith) (by linarith)
                have hw5 : (7791189/50000000000:ℝ) ≤ wfun (x + y + z) := wc_1059 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (17153/16384:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
                have hw4 : (60351447/10000000000000:ℝ) ≤ wfun (y + z) := wc_453 (y + z) (by linarith) (by linarith)
                have hw5 : (7791189/50000000000:ℝ) ≤ wfun (x + y + z) := wc_1059 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
                have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
                have hw4 : (16140217/2500000000000:ℝ) ≤ wfun (y + z) := wc_455 (y + z) (by linarith) (by linarith)
                have hw5 : (31466501/200000000000:ℝ) ≤ wfun (x + y + z) := wc_1071 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (17163/16384:ℝ) with hc | hc
          · rcases le_total y (32481/16384:ℝ) with hc | hc
            · rcases le_total z (17163/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (16140217/2500000000000:ℝ) ≤ wfun (y + z) := wc_455 (y + z) (by linarith) (by linarith)
                have hw5 : (7791189/50000000000:ℝ) ≤ wfun (x + y + z) := wc_1059 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (68911149/10000000000000:ℝ) ≤ wfun (y + z) := wc_459 (y + z) (by linarith) (by linarith)
                have hw5 : (31466501/200000000000:ℝ) ≤ wfun (x + y + z) := wc_1071 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
              have hw4 : (68883243/10000000000000:ℝ) ≤ wfun (y + z) := wc_460 (y + z) (by linarith) (by linarith)
              have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32481/16384:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
              have hw4 : (64534721/10000000000000:ℝ) ≤ wfun (y + z) := wc_456 (y + z) (by linarith) (by linarith)
              have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
              have hw4 : (68883243/10000000000000:ℝ) ≤ wfun (y + z) := wc_460 (y + z) (by linarith) (by linarith)
              have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (8579/8192:ℝ) with hc | hc
        · rcases le_total x (17163/16384:ℝ) with hc | hc
          · rcases le_total y (32491/16384:ℝ) with hc | hc
            · rcases le_total z (17153/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
                have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
                have hw4 : (16140217/2500000000000:ℝ) ≤ wfun (y + z) := wc_455 (y + z) (by linarith) (by linarith)
                have hw5 : (7791189/50000000000:ℝ) ≤ wfun (x + y + z) := wc_1059 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
                have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
                have hw4 : (68911149/10000000000000:ℝ) ≤ wfun (y + z) := wc_459 (y + z) (by linarith) (by linarith)
                have hw5 : (31466501/200000000000:ℝ) ≤ wfun (x + y + z) := wc_1071 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
              have hw4 : (68883243/10000000000000:ℝ) ≤ wfun (y + z) := wc_460 (y + z) (by linarith) (by linarith)
              have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32491/16384:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
              have hw4 : (64534721/10000000000000:ℝ) ≤ wfun (y + z) := wc_456 (y + z) (by linarith) (by linarith)
              have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (82806113/10000000000000:ℝ) ≤ wfun (x + y) := wc_469 (x + y) (by linarith) (by linarith)
              have hw4 : (68883243/10000000000000:ℝ) ≤ wfun (y + z) := wc_460 (y + z) (by linarith) (by linarith)
              have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17163/16384:ℝ) with hc | hc
          · rcases le_total y (32491/16384:ℝ) with hc | hc
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
              have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
              have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
              have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
              have hw5 : (1603220471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1079 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32491/16384:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
              have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
              have hw5 : (1603220471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1079 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (82806113/10000000000000:ℝ) ≤ wfun (x + y) := wc_469 (x + y) (by linarith) (by linarith)
              have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
              have hw5 : (1618505281/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1081 (x + y + z) (by linarith) (by linarith)
              linarith

set_option maxHeartbeats 20000000 in
lemma ch_128 (x y z : ℝ) (hx1 : (2141/2048:ℝ) ≤ x) (hx2 : x ≤ (4287/4096:ℝ))
    (hy1 : (2031/1024:ℝ) ≤ y) (hy2 : y ≤ (8129/4096:ℝ))
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
    · rcases le_total y (16253/8192:ℝ) with hc | hc
      · rcases le_total z (8569/8192:ℝ) with hc | hc
        · rcases le_total x (17133/16384:ℝ) with hc | hc
          · rcases le_total y (32501/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (3962835597/10000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
              have hw4 : (56260189/10000000000000:ℝ) ≤ wfun (y + z) := wc_446 (y + z) (by linarith) (by linarith)
              have hw5 : (719773133/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1006 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (488744817/1250000000000:ℝ) ≤ wfun y := wc_197 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
              have hw4 : (30163501/5000000000000:ℝ) ≤ wfun (y + z) := wc_454 (y + z) (by linarith) (by linarith)
              have hw5 : (1454086357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1027 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32501/16384:ℝ) with hc | hc
            · rcases le_total z (17133/16384:ℝ) with hc | hc
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                have hw1 : (3962835597/10000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
                have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (14070747/2500000000000:ℝ) ≤ wfun (y + z) := wc_445 (y + z) (by linarith) (by linarith)
                have hw5 : (363630819/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1026 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                have hw1 : (3962835597/10000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (60351447/10000000000000:ℝ) ≤ wfun (y + z) := wc_453 (y + z) (by linarith) (by linarith)
                have hw5 : (73456793/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1029 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (488744817/1250000000000:ℝ) ≤ wfun y := wc_197 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
              have hw4 : (30163501/5000000000000:ℝ) ≤ wfun (y + z) := wc_454 (y + z) (by linarith) (by linarith)
              have hw5 : (293738917/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1030 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17133/16384:ℝ) with hc | hc
          · rcases le_total y (32501/16384:ℝ) with hc | hc
            · rcases le_total z (17143/16384:ℝ) with hc | hc
              · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                have hw1 : (3962835597/10000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
                have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
                have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
                have hw4 : (16140217/2500000000000:ℝ) ≤ wfun (y + z) := wc_455 (y + z) (by linarith) (by linarith)
                have hw5 : (73456793/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1029 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                have hw1 : (3962835597/10000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
                have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
                have hw4 : (68911149/10000000000000:ℝ) ≤ wfun (y + z) := wc_459 (y + z) (by linarith) (by linarith)
                have hw5 : (296763303/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1035 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (488744817/1250000000000:ℝ) ≤ wfun y := wc_197 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
              have hw4 : (68883243/10000000000000:ℝ) ≤ wfun (y + z) := wc_460 (y + z) (by linarith) (by linarith)
              have hw5 : (1483370863/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1036 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32501/16384:ℝ) with hc | hc
            · rcases le_total z (17143/16384:ℝ) with hc | hc
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                have hw1 : (3962835597/10000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
                have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (16140217/2500000000000:ℝ) ≤ wfun (y + z) := wc_455 (y + z) (by linarith) (by linarith)
                have hw5 : (296763303/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1035 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                have hw1 : (3962835597/10000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (68911149/10000000000000:ℝ) ≤ wfun (y + z) := wc_459 (y + z) (by linarith) (by linarith)
                have hw5 : (1498565153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1038 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (488744817/1250000000000:ℝ) ≤ wfun y := wc_197 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
              have hw4 : (68883243/10000000000000:ℝ) ≤ wfun (y + z) := wc_460 (y + z) (by linarith) (by linarith)
              have hw5 : (749057553/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1039 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (8569/8192:ℝ) with hc | hc
        · rcases le_total x (17133/16384:ℝ) with hc | hc
          · rcases le_total y (32511/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (3857446169/10000000000000:ℝ) ≤ wfun y := wc_198 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
              have hw4 : (64534721/10000000000000:ℝ) ≤ wfun (y + z) := wc_456 (y + z) (by linarith) (by linarith)
              have hw5 : (293738917/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1030 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (951324587/2500000000000:ℝ) ≤ wfun y := wc_200 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
              have hw4 : (68883243/10000000000000:ℝ) ≤ wfun (y + z) := wc_460 (y + z) (by linarith) (by linarith)
              have hw5 : (1483370863/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1036 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32511/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (3857446169/10000000000000:ℝ) ≤ wfun y := wc_198 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
              have hw4 : (64534721/10000000000000:ℝ) ≤ wfun (y + z) := wc_456 (y + z) (by linarith) (by linarith)
              have hw5 : (1483370863/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1036 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (951324587/2500000000000:ℝ) ≤ wfun y := wc_200 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
              have hw4 : (68883243/10000000000000:ℝ) ≤ wfun (y + z) := wc_460 (y + z) (by linarith) (by linarith)
              have hw5 : (749057553/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1039 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17133/16384:ℝ) with hc | hc
          · rcases le_total y (32511/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (3857446169/10000000000000:ℝ) ≤ wfun y := wc_198 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
              have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
              have hw5 : (749057553/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1039 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (951324587/2500000000000:ℝ) ≤ wfun y := wc_200 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
              have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
              have hw5 : (60517089/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1048 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32511/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (3857446169/10000000000000:ℝ) ≤ wfun y := wc_198 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
              have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
              have hw5 : (60517089/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1048 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (951324587/2500000000000:ℝ) ≤ wfun y := wc_200 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
              have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
              have hw5 : (305561427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1051 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total y (16253/8192:ℝ) with hc | hc
      · rcases le_total z (8569/8192:ℝ) with hc | hc
        · rcases le_total x (17143/16384:ℝ) with hc | hc
          · rcases le_total y (32501/16384:ℝ) with hc | hc
            · rcases le_total z (17133/16384:ℝ) with hc | hc
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (3962835597/10000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
                have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (14070747/2500000000000:ℝ) ≤ wfun (y + z) := wc_445 (y + z) (by linarith) (by linarith)
                have hw5 : (73456793/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1029 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (3962835597/10000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (60351447/10000000000000:ℝ) ≤ wfun (y + z) := wc_453 (y + z) (by linarith) (by linarith)
                have hw5 : (296763303/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1035 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (488744817/1250000000000:ℝ) ≤ wfun y := wc_197 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
              have hw4 : (30163501/5000000000000:ℝ) ≤ wfun (y + z) := wc_454 (y + z) (by linarith) (by linarith)
              have hw5 : (1483370863/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1036 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32501/16384:ℝ) with hc | hc
            · rcases le_total z (17133/16384:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (3962835597/10000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
                have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
                have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                have hw4 : (14070747/2500000000000:ℝ) ≤ wfun (y + z) := wc_445 (y + z) (by linarith) (by linarith)
                have hw5 : (296763303/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1035 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (3962835597/10000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
                have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                have hw4 : (60351447/10000000000000:ℝ) ≤ wfun (y + z) := wc_453 (y + z) (by linarith) (by linarith)
                have hw5 : (1498565153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1038 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (488744817/1250000000000:ℝ) ≤ wfun y := wc_197 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
              have hw4 : (30163501/5000000000000:ℝ) ≤ wfun (y + z) := wc_454 (y + z) (by linarith) (by linarith)
              have hw5 : (749057553/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1039 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17143/16384:ℝ) with hc | hc
          · rcases le_total y (32501/16384:ℝ) with hc | hc
            · rcases le_total z (17143/16384:ℝ) with hc | hc
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (3962835597/10000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
                have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (16140217/2500000000000:ℝ) ≤ wfun (y + z) := wc_455 (y + z) (by linarith) (by linarith)
                have hw5 : (1498565153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1038 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (3962835597/10000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (68911149/10000000000000:ℝ) ≤ wfun (y + z) := wc_459 (y + z) (by linarith) (by linarith)
                have hw5 : (189172711/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1047 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (17143/16384:ℝ) with hc | hc
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (488744817/1250000000000:ℝ) ≤ wfun y := wc_197 y (by linarith) (by linarith)
                have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
                have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                have hw4 : (68911149/10000000000000:ℝ) ≤ wfun (y + z) := wc_459 (y + z) (by linarith) (by linarith)
                have hw5 : (189172711/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1047 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (488744817/1250000000000:ℝ) ≤ wfun y := wc_197 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
                have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                have hw4 : (73402187/10000000000000:ℝ) ≤ wfun (y + z) := wc_461 (y + z) (by linarith) (by linarith)
                have hw5 : (1528266033/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1050 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (32501/16384:ℝ) with hc | hc
            · rcases le_total z (17143/16384:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (3962835597/10000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
                have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
                have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                have hw4 : (16140217/2500000000000:ℝ) ≤ wfun (y + z) := wc_455 (y + z) (by linarith) (by linarith)
                have hw5 : (189172711/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1047 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (3962835597/10000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
                have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                have hw4 : (68911149/10000000000000:ℝ) ≤ wfun (y + z) := wc_459 (y + z) (by linarith) (by linarith)
                have hw5 : (1528266033/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1050 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (488744817/1250000000000:ℝ) ≤ wfun y := wc_197 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
              have hw4 : (68883243/10000000000000:ℝ) ≤ wfun (y + z) := wc_460 (y + z) (by linarith) (by linarith)
              have hw5 : (305561427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1051 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (8569/8192:ℝ) with hc | hc
        · rcases le_total x (17143/16384:ℝ) with hc | hc
          · rcases le_total y (32511/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (3857446169/10000000000000:ℝ) ≤ wfun y := wc_198 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
              have hw4 : (64534721/10000000000000:ℝ) ≤ wfun (y + z) := wc_456 (y + z) (by linarith) (by linarith)
              have hw5 : (749057553/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1039 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (951324587/2500000000000:ℝ) ≤ wfun y := wc_200 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
              have hw4 : (68883243/10000000000000:ℝ) ≤ wfun (y + z) := wc_460 (y + z) (by linarith) (by linarith)
              have hw5 : (60517089/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1048 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32511/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (3857446169/10000000000000:ℝ) ≤ wfun y := wc_198 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
              have hw4 : (64534721/10000000000000:ℝ) ≤ wfun (y + z) := wc_456 (y + z) (by linarith) (by linarith)
              have hw5 : (60517089/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1048 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (951324587/2500000000000:ℝ) ≤ wfun y := wc_200 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (82806113/10000000000000:ℝ) ≤ wfun (x + y) := wc_469 (x + y) (by linarith) (by linarith)
              have hw4 : (68883243/10000000000000:ℝ) ≤ wfun (y + z) := wc_460 (y + z) (by linarith) (by linarith)
              have hw5 : (305561427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1051 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17143/16384:ℝ) with hc | hc
          · rcases le_total y (32511/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (3857446169/10000000000000:ℝ) ≤ wfun y := wc_198 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
              have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
              have hw5 : (305561427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1051 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (951324587/2500000000000:ℝ) ≤ wfun y := wc_200 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
              have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
              have hw5 : (1542754747/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1057 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32511/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (3857446169/10000000000000:ℝ) ≤ wfun y := wc_198 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
              have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
              have hw5 : (1542754747/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1057 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (951324587/2500000000000:ℝ) ≤ wfun y := wc_200 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (82806113/10000000000000:ℝ) ≤ wfun (x + y) := wc_469 (x + y) (by linarith) (by linarith)
              have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
              have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
              linarith
  · rcases le_total x (8569/8192:ℝ) with hc | hc
    · rcases le_total y (16253/8192:ℝ) with hc | hc
      · rcases le_total z (8579/8192:ℝ) with hc | hc
        · rcases le_total x (17133/16384:ℝ) with hc | hc
          · rcases le_total y (32501/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (3962835597/10000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
              have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
              have hw5 : (749057553/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1039 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (488744817/1250000000000:ℝ) ≤ wfun y := wc_197 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
              have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
              have hw5 : (60517089/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1048 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32501/16384:ℝ) with hc | hc
            · rcases le_total z (17153/16384:ℝ) with hc | hc
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                have hw1 : (3962835597/10000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
                have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (73402187/10000000000000:ℝ) ≤ wfun (y + z) := wc_461 (y + z) (by linarith) (by linarith)
                have hw5 : (189172711/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1047 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                have hw1 : (3962835597/10000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (19508469/2500000000000:ℝ) ≤ wfun (y + z) := wc_467 (y + z) (by linarith) (by linarith)
                have hw5 : (1528266033/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1050 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (488744817/1250000000000:ℝ) ≤ wfun y := wc_197 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
              have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
              have hw5 : (305561427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1051 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17133/16384:ℝ) with hc | hc
          · rcases le_total y (32501/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (3962835597/10000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
              have hw4 : (8277259/1000000000000:ℝ) ≤ wfun (y + z) := wc_470 (y + z) (by linarith) (by linarith)
              have hw5 : (305561427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1051 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (488744817/1250000000000:ℝ) ≤ wfun y := wc_197 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
              have hw4 : (17536657/2000000000000:ℝ) ≤ wfun (y + z) := wc_474 (y + z) (by linarith) (by linarith)
              have hw5 : (1542754747/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1057 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32501/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (3962835597/10000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
              have hw4 : (8277259/1000000000000:ℝ) ≤ wfun (y + z) := wc_470 (y + z) (by linarith) (by linarith)
              have hw5 : (1542754747/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1057 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (488744817/1250000000000:ℝ) ≤ wfun y := wc_197 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
              have hw4 : (17536657/2000000000000:ℝ) ≤ wfun (y + z) := wc_474 (y + z) (by linarith) (by linarith)
              have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (8579/8192:ℝ) with hc | hc
        · rcases le_total x (17133/16384:ℝ) with hc | hc
          · rcases le_total y (32511/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (3857446169/10000000000000:ℝ) ≤ wfun y := wc_198 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
              have hw4 : (8277259/1000000000000:ℝ) ≤ wfun (y + z) := wc_470 (y + z) (by linarith) (by linarith)
              have hw5 : (305561427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1051 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (951324587/2500000000000:ℝ) ≤ wfun y := wc_200 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
              have hw4 : (17536657/2000000000000:ℝ) ≤ wfun (y + z) := wc_474 (y + z) (by linarith) (by linarith)
              have hw5 : (1542754747/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1057 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32511/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (3857446169/10000000000000:ℝ) ≤ wfun y := wc_198 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
              have hw4 : (8277259/1000000000000:ℝ) ≤ wfun (y + z) := wc_470 (y + z) (by linarith) (by linarith)
              have hw5 : (1542754747/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1057 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (951324587/2500000000000:ℝ) ≤ wfun y := wc_200 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
              have hw4 : (17536657/2000000000000:ℝ) ≤ wfun (y + z) := wc_474 (y + z) (by linarith) (by linarith)
              have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17133/16384:ℝ) with hc | hc
          · rcases le_total y (32511/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (3857446169/10000000000000:ℝ) ≤ wfun y := wc_198 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
              have hw4 : (92734261/10000000000000:ℝ) ≤ wfun (y + z) := wc_476 (y + z) (by linarith) (by linarith)
              have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (951324587/2500000000000:ℝ) ≤ wfun y := wc_200 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
              have hw4 : (97925413/10000000000000:ℝ) ≤ wfun (y + z) := wc_495 (y + z) (by linarith) (by linarith)
              have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32511/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (3857446169/10000000000000:ℝ) ≤ wfun y := wc_198 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
              have hw4 : (92734261/10000000000000:ℝ) ≤ wfun (y + z) := wc_476 (y + z) (by linarith) (by linarith)
              have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (951324587/2500000000000:ℝ) ≤ wfun y := wc_200 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
              have hw4 : (97925413/10000000000000:ℝ) ≤ wfun (y + z) := wc_495 (y + z) (by linarith) (by linarith)
              have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total y (16253/8192:ℝ) with hc | hc
      · rcases le_total z (8579/8192:ℝ) with hc | hc
        · rcases le_total x (17143/16384:ℝ) with hc | hc
          · rcases le_total y (32501/16384:ℝ) with hc | hc
            · rcases le_total z (17153/16384:ℝ) with hc | hc
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (3962835597/10000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
                have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (73402187/10000000000000:ℝ) ≤ wfun (y + z) := wc_461 (y + z) (by linarith) (by linarith)
                have hw5 : (1528266033/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1050 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (3962835597/10000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (19508469/2500000000000:ℝ) ≤ wfun (y + z) := wc_467 (y + z) (by linarith) (by linarith)
                have hw5 : (15432181/100000000000:ℝ) ≤ wfun (x + y + z) := wc_1056 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (488744817/1250000000000:ℝ) ≤ wfun y := wc_197 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
              have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
              have hw5 : (1542754747/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1057 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32501/16384:ℝ) with hc | hc
            · rcases le_total z (17153/16384:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (3962835597/10000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
                have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                have hw4 : (73402187/10000000000000:ℝ) ≤ wfun (y + z) := wc_461 (y + z) (by linarith) (by linarith)
                have hw5 : (15432181/100000000000:ℝ) ≤ wfun (x + y + z) := wc_1056 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (3962835597/10000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
                have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                have hw4 : (19508469/2500000000000:ℝ) ≤ wfun (y + z) := wc_467 (y + z) (by linarith) (by linarith)
                have hw5 : (7791189/50000000000:ℝ) ≤ wfun (x + y + z) := wc_1059 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (488744817/1250000000000:ℝ) ≤ wfun y := wc_197 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
              have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
              have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17143/16384:ℝ) with hc | hc
          · rcases le_total y (32501/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (3962835597/10000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
              have hw4 : (8277259/1000000000000:ℝ) ≤ wfun (y + z) := wc_470 (y + z) (by linarith) (by linarith)
              have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (488744817/1250000000000:ℝ) ≤ wfun y := wc_197 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
              have hw4 : (17536657/2000000000000:ℝ) ≤ wfun (y + z) := wc_474 (y + z) (by linarith) (by linarith)
              have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32501/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (3962835597/10000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
              have hw4 : (8277259/1000000000000:ℝ) ≤ wfun (y + z) := wc_470 (y + z) (by linarith) (by linarith)
              have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (488744817/1250000000000:ℝ) ≤ wfun y := wc_197 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
              have hw4 : (17536657/2000000000000:ℝ) ≤ wfun (y + z) := wc_474 (y + z) (by linarith) (by linarith)
              have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (8579/8192:ℝ) with hc | hc
        · rcases le_total x (17143/16384:ℝ) with hc | hc
          · rcases le_total y (32511/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (3857446169/10000000000000:ℝ) ≤ wfun y := wc_198 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
              have hw4 : (8277259/1000000000000:ℝ) ≤ wfun (y + z) := wc_470 (y + z) (by linarith) (by linarith)
              have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (951324587/2500000000000:ℝ) ≤ wfun y := wc_200 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
              have hw4 : (17536657/2000000000000:ℝ) ≤ wfun (y + z) := wc_474 (y + z) (by linarith) (by linarith)
              have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32511/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (3857446169/10000000000000:ℝ) ≤ wfun y := wc_198 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
              have hw4 : (8277259/1000000000000:ℝ) ≤ wfun (y + z) := wc_470 (y + z) (by linarith) (by linarith)
              have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (951324587/2500000000000:ℝ) ≤ wfun y := wc_200 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (82806113/10000000000000:ℝ) ≤ wfun (x + y) := wc_469 (x + y) (by linarith) (by linarith)
              have hw4 : (17536657/2000000000000:ℝ) ≤ wfun (y + z) := wc_474 (y + z) (by linarith) (by linarith)
              have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17143/16384:ℝ) with hc | hc
          · rcases le_total y (32511/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (3857446169/10000000000000:ℝ) ≤ wfun y := wc_198 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
              have hw4 : (92734261/10000000000000:ℝ) ≤ wfun (y + z) := wc_476 (y + z) (by linarith) (by linarith)
              have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (951324587/2500000000000:ℝ) ≤ wfun y := wc_200 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
              have hw4 : (97925413/10000000000000:ℝ) ≤ wfun (y + z) := wc_495 (y + z) (by linarith) (by linarith)
              have hw5 : (1603220471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1079 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32511/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (3857446169/10000000000000:ℝ) ≤ wfun y := wc_198 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
              have hw4 : (92734261/10000000000000:ℝ) ≤ wfun (y + z) := wc_476 (y + z) (by linarith) (by linarith)
              have hw5 : (1603220471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1079 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (951324587/2500000000000:ℝ) ≤ wfun y := wc_200 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (82806113/10000000000000:ℝ) ≤ wfun (x + y) := wc_469 (x + y) (by linarith) (by linarith)
              have hw4 : (97925413/10000000000000:ℝ) ≤ wfun (y + z) := wc_495 (y + z) (by linarith) (by linarith)
              have hw5 : (1618505281/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1081 (x + y + z) (by linarith) (by linarith)
              linarith

set_option maxHeartbeats 20000000 in
lemma ch_155 (x y z : ℝ) (hx1 : (2151/2048:ℝ) ≤ x) (hx2 : x ≤ (539/512:ℝ))
    (hy1 : (1013/512:ℝ) ≤ y) (hy2 : y ≤ (2031/1024:ℝ))
    (hz1 : (1073/1024:ℝ) ≤ z) (hz2 : z ≤ (539/512:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total y (4057/2048:ℝ) with hc | hc
  · rcases le_total z (2151/2048:ℝ) with hc | hc
    · rcases le_total x (4307/4096:ℝ) with hc | hc
      · rcases le_total y (8109/4096:ℝ) with hc | hc
        · rcases le_total z (4297/4096:ℝ) with hc | hc
          · rcases le_total x (8609/8192:ℝ) with hc | hc
            · rcases le_total y (16213/8192:ℝ) with hc | hc
              · rcases le_total z (8589/8192:ℝ) with hc | hc
                · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                  have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
                  have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
                  have hw5 : (778417423/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1062 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                  have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                  have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
                  have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
                  have hw5 : (1587049791/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1076 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (8589/8192:ℝ) with hc | hc
                · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                  have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
                  have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
                  have hw5 : (1587049791/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1076 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                  have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                  have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
                  have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
                  have hw5 : (1617533987/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1083 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total y (16213/8192:ℝ) with hc | hc
              · rcases le_total z (8589/8192:ℝ) with hc | hc
                · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                  have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
                  have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
                  have hw5 : (1587049791/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1076 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                  have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                  have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
                  have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
                  have hw5 : (1617533987/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1083 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (8589/8192:ℝ) with hc | hc
                · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                  have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
                  have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
                  have hw5 : (1617533987/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1083 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                  have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                  have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
                  have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
                  have hw5 : (65931469/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1093 (x + y + z) (by linarith) (by linarith)
                  linarith
          · rcases le_total x (8609/8192:ℝ) with hc | hc
            · rcases le_total y (16213/8192:ℝ) with hc | hc
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
                have hw4 : (4135373/1000000000000:ℝ) ≤ wfun (y + z) := wc_434 (y + z) (by linarith) (by linarith)
                have hw5 : (1616563421/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1084 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
                have hw4 : (48490713/10000000000000:ℝ) ≤ wfun (y + z) := wc_442 (y + z) (by linarith) (by linarith)
                have hw5 : (25739029/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1094 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16213/8192:ℝ) with hc | hc
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
                have hw4 : (4135373/1000000000000:ℝ) ≤ wfun (y + z) := wc_434 (y + z) (by linarith) (by linarith)
                have hw5 : (25739029/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1094 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
                have hw4 : (48490713/10000000000000:ℝ) ≤ wfun (y + z) := wc_442 (y + z) (by linarith) (by linarith)
                have hw5 : (26223437/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1100 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (4297/4096:ℝ) with hc | hc
          · rcases le_total x (8609/8192:ℝ) with hc | hc
            · rcases le_total y (16223/8192:ℝ) with hc | hc
              · rcases le_total z (8589/8192:ℝ) with hc | hc
                · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                  have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
                  have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
                  have hw5 : (1617533987/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1083 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                  have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                  have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
                  have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
                  have hw5 : (65931469/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1093 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (8589/8192:ℝ) with hc | hc
                · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                  have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
                  have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
                  have hw5 : (65931469/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1093 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                  have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                  have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
                  have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
                  have hw5 : (52478353/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1099 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total y (16223/8192:ℝ) with hc | hc
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
                have hw4 : (4135373/1000000000000:ℝ) ≤ wfun (y + z) := wc_434 (y + z) (by linarith) (by linarith)
                have hw5 : (25739029/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1094 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
                have hw4 : (48490713/10000000000000:ℝ) ≤ wfun (y + z) := wc_442 (y + z) (by linarith) (by linarith)
                have hw5 : (26223437/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1100 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (8609/8192:ℝ) with hc | hc
            · rcases le_total y (16223/8192:ℝ) with hc | hc
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
                have hw4 : (2809593/500000000000:ℝ) ≤ wfun (y + z) := wc_448 (y + z) (by linarith) (by linarith)
                have hw5 : (26223437/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1100 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
                have hw4 : (64456359/10000000000000:ℝ) ≤ wfun (y + z) := wc_458 (y + z) (by linarith) (by linarith)
                have hw5 : (1709569043/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1114 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16223/8192:ℝ) with hc | hc
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
                have hw4 : (2809593/500000000000:ℝ) ≤ wfun (y + z) := wc_448 (y + z) (by linarith) (by linarith)
                have hw5 : (1709569043/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1114 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
                have hw4 : (64456359/10000000000000:ℝ) ≤ wfun (y + z) := wc_458 (y + z) (by linarith) (by linarith)
                have hw5 : (870552183/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1119 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total y (8109/4096:ℝ) with hc | hc
        · rcases le_total z (4297/4096:ℝ) with hc | hc
          · rcases le_total x (8619/8192:ℝ) with hc | hc
            · rcases le_total y (16213/8192:ℝ) with hc | hc
              · have hw0 : (25860883/1250000000000:ℝ) ≤ wfun x := wc_88 x (by linarith) (by linarith)
                have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
                have hw4 : (28775469/10000000000000:ℝ) ≤ wfun (y + z) := wc_416 (y + z) (by linarith) (by linarith)
                have hw5 : (1616563421/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1084 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (25860883/1250000000000:ℝ) ≤ wfun x := wc_88 x (by linarith) (by linarith)
                have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
                have hw4 : (6956343/2000000000000:ℝ) ≤ wfun (y + z) := wc_428 (y + z) (by linarith) (by linarith)
                have hw5 : (25739029/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1094 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16213/8192:ℝ) with hc | hc
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_90 x (by linarith) (by linarith)
                have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
                have hw4 : (28775469/10000000000000:ℝ) ≤ wfun (y + z) := wc_416 (y + z) (by linarith) (by linarith)
                have hw5 : (25739029/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1094 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_90 x (by linarith) (by linarith)
                have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
                have hw4 : (6956343/2000000000000:ℝ) ≤ wfun (y + z) := wc_428 (y + z) (by linarith) (by linarith)
                have hw5 : (26223437/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1100 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (8619/8192:ℝ) with hc | hc
            · rcases le_total y (16213/8192:ℝ) with hc | hc
              · have hw0 : (25860883/1250000000000:ℝ) ≤ wfun x := wc_88 x (by linarith) (by linarith)
                have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
                have hw4 : (4135373/1000000000000:ℝ) ≤ wfun (y + z) := wc_434 (y + z) (by linarith) (by linarith)
                have hw5 : (26223437/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1100 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (25860883/1250000000000:ℝ) ≤ wfun x := wc_88 x (by linarith) (by linarith)
                have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
                have hw4 : (48490713/10000000000000:ℝ) ≤ wfun (y + z) := wc_442 (y + z) (by linarith) (by linarith)
                have hw5 : (1709569043/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1114 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_90 x (by linarith) (by linarith)
              have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_162 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
              have hw3 : (82672123/10000000000000:ℝ) ≤ wfun (x + y) := wc_472 (x + y) (by linarith) (by linarith)
              have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_435 (y + z) (by linarith) (by linarith)
              have hw5 : (1708543871/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1115 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (4297/4096:ℝ) with hc | hc
          · rcases le_total x (8619/8192:ℝ) with hc | hc
            · rcases le_total y (16223/8192:ℝ) with hc | hc
              · have hw0 : (25860883/1250000000000:ℝ) ≤ wfun x := wc_88 x (by linarith) (by linarith)
                have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
                have hw4 : (4135373/1000000000000:ℝ) ≤ wfun (y + z) := wc_434 (y + z) (by linarith) (by linarith)
                have hw5 : (26223437/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1100 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (25860883/1250000000000:ℝ) ≤ wfun x := wc_88 x (by linarith) (by linarith)
                have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
                have hw4 : (48490713/10000000000000:ℝ) ≤ wfun (y + z) := wc_442 (y + z) (by linarith) (by linarith)
                have hw5 : (1709569043/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1114 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_90 x (by linarith) (by linarith)
              have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_172 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
              have hw3 : (25782839/2500000000000:ℝ) ≤ wfun (x + y) := wc_499 (x + y) (by linarith) (by linarith)
              have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_435 (y + z) (by linarith) (by linarith)
              have hw5 : (1708543871/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1115 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (8619/8192:ℝ) with hc | hc
            · have hw0 : (25860883/1250000000000:ℝ) ≤ wfun x := wc_88 x (by linarith) (by linarith)
              have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_172 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
              have hw3 : (46310863/5000000000000:ℝ) ≤ wfun (x + y) := wc_478 (x + y) (by linarith) (by linarith)
              have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_449 (y + z) (by linarith) (by linarith)
              have hw5 : (43501511/250000000000:ℝ) ≤ wfun (x + y + z) := wc_1120 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_90 x (by linarith) (by linarith)
              have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_172 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
              have hw3 : (25782839/2500000000000:ℝ) ≤ wfun (x + y) := wc_499 (x + y) (by linarith) (by linarith)
              have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_449 (y + z) (by linarith) (by linarith)
              have hw5 : (1771842379/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1126 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total x (4307/4096:ℝ) with hc | hc
      · rcases le_total y (8109/4096:ℝ) with hc | hc
        · rcases le_total z (4307/4096:ℝ) with hc | hc
          · rcases le_total x (8609/8192:ℝ) with hc | hc
            · rcases le_total y (16213/8192:ℝ) with hc | hc
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
                have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
                have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
                have hw4 : (2809593/500000000000:ℝ) ≤ wfun (y + z) := wc_448 (y + z) (by linarith) (by linarith)
                have hw5 : (26223437/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1100 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
                have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
                have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
                have hw4 : (64456359/10000000000000:ℝ) ≤ wfun (y + z) := wc_458 (y + z) (by linarith) (by linarith)
                have hw5 : (1709569043/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1114 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
              have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_162 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
              have hw3 : (64456359/10000000000000:ℝ) ≤ wfun (x + y) := wc_458 (x + y) (by linarith) (by linarith)
              have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_449 (y + z) (by linarith) (by linarith)
              have hw5 : (1708543871/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1115 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
            have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_162 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_449 (x + y) (by linarith) (by linarith)
            have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_465 (y + z) (by linarith) (by linarith)
            have hw5 : (1739017297/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1121 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (4307/4096:ℝ) with hc | hc
          · rcases le_total x (8609/8192:ℝ) with hc | hc
            · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
              have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_172 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
              have hw3 : (73283389/10000000000000:ℝ) ≤ wfun (x + y) := wc_464 (x + y) (by linarith) (by linarith)
              have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_465 (y + z) (by linarith) (by linarith)
              have hw5 : (43501511/250000000000:ℝ) ≤ wfun (x + y + z) := wc_1120 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
              have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_172 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
              have hw3 : (82672123/10000000000000:ℝ) ≤ wfun (x + y) := wc_472 (x + y) (by linarith) (by linarith)
              have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_465 (y + z) (by linarith) (by linarith)
              have hw5 : (1771842379/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1126 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
            have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_172 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_465 (x + y) (by linarith) (by linarith)
            have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_479 (y + z) (by linarith) (by linarith)
            have hw5 : (112675493/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1130 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total y (8109/4096:ℝ) with hc | hc
        · rcases le_total z (4307/4096:ℝ) with hc | hc
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
            have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_162 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_465 (x + y) (by linarith) (by linarith)
            have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_449 (y + z) (by linarith) (by linarith)
            have hw5 : (1739017297/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1121 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
            have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_162 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_465 (x + y) (by linarith) (by linarith)
            have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_465 (y + z) (by linarith) (by linarith)
            have hw5 : (112675493/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1130 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (4307/4096:ℝ) with hc | hc
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
            have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_172 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_479 (x + y) (by linarith) (by linarith)
            have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_465 (y + z) (by linarith) (by linarith)
            have hw5 : (112675493/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1130 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
            have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_172 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_479 (x + y) (by linarith) (by linarith)
            have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_479 (y + z) (by linarith) (by linarith)
            have hw5 : (933826779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1140 (x + y + z) (by linarith) (by linarith)
            linarith
  · rcases le_total z (2151/2048:ℝ) with hc | hc
    · rcases le_total x (4307/4096:ℝ) with hc | hc
      · rcases le_total y (8119/4096:ℝ) with hc | hc
        · rcases le_total z (4297/4096:ℝ) with hc | hc
          · rcases le_total x (8609/8192:ℝ) with hc | hc
            · rcases le_total y (16233/8192:ℝ) with hc | hc
              · rcases le_total z (8589/8192:ℝ) with hc | hc
                · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                  have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
                  have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
                  have hw5 : (52478353/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1099 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                  have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                  have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
                  have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
                  have hw5 : (342118997/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1113 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (8589/8192:ℝ) with hc | hc
                · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                  have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
                  have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
                  have hw5 : (342118997/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1113 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                  have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                  have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
                  have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
                  have hw5 : (69685963/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1118 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total y (16233/8192:ℝ) with hc | hc
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
                have hw4 : (2809593/500000000000:ℝ) ≤ wfun (y + z) := wc_448 (y + z) (by linarith) (by linarith)
                have hw5 : (1709569043/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1114 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
                have hw4 : (64456359/10000000000000:ℝ) ≤ wfun (y + z) := wc_458 (y + z) (by linarith) (by linarith)
                have hw5 : (870552183/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1119 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (8609/8192:ℝ) with hc | hc
            · rcases le_total y (16233/8192:ℝ) with hc | hc
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
                have hw4 : (73283389/10000000000000:ℝ) ≤ wfun (y + z) := wc_464 (y + z) (by linarith) (by linarith)
                have hw5 : (870552183/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1119 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
                have hw4 : (82672123/10000000000000:ℝ) ≤ wfun (y + z) := wc_472 (y + z) (by linarith) (by linarith)
                have hw5 : (1772905213/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1125 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16233/8192:ℝ) with hc | hc
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
                have hw4 : (73283389/10000000000000:ℝ) ≤ wfun (y + z) := wc_464 (y + z) (by linarith) (by linarith)
                have hw5 : (1772905213/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1125 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
                have hw4 : (82672123/10000000000000:ℝ) ≤ wfun (y + z) := wc_472 (y + z) (by linarith) (by linarith)
                have hw5 : (112810679/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1128 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (4297/4096:ℝ) with hc | hc
          · rcases le_total x (8609/8192:ℝ) with hc | hc
            · rcases le_total y (16243/8192:ℝ) with hc | hc
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
                have hw4 : (73283389/10000000000000:ℝ) ≤ wfun (y + z) := wc_464 (y + z) (by linarith) (by linarith)
                have hw5 : (870552183/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1119 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
                have hw4 : (82672123/10000000000000:ℝ) ≤ wfun (y + z) := wc_472 (y + z) (by linarith) (by linarith)
                have hw5 : (1772905213/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1125 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16243/8192:ℝ) with hc | hc
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
                have hw4 : (73283389/10000000000000:ℝ) ≤ wfun (y + z) := wc_464 (y + z) (by linarith) (by linarith)
                have hw5 : (1772905213/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1125 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
                have hw4 : (82672123/10000000000000:ℝ) ≤ wfun (y + z) := wc_472 (y + z) (by linarith) (by linarith)
                have hw5 : (112810679/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1128 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (8609/8192:ℝ) with hc | hc
            · rcases le_total y (16243/8192:ℝ) with hc | hc
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
                have hw4 : (46310863/5000000000000:ℝ) ≤ wfun (y + z) := wc_478 (y + z) (by linarith) (by linarith)
                have hw5 : (112810679/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1128 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
                have hw4 : (25782839/2500000000000:ℝ) ≤ wfun (y + z) := wc_499 (y + z) (by linarith) (by linarith)
                have hw5 : (183730059/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_1136 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
              have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
              have hw3 : (15728411/1250000000000:ℝ) ≤ wfun (x + y) := wc_511 (x + y) (by linarith) (by linarith)
              have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_479 (y + z) (by linarith) (by linarith)
              have hw5 : (1836199483/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1137 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total y (8119/4096:ℝ) with hc | hc
        · rcases le_total z (4297/4096:ℝ) with hc | hc
          · rcases le_total x (8619/8192:ℝ) with hc | hc
            · rcases le_total y (16233/8192:ℝ) with hc | hc
              · have hw0 : (25860883/1250000000000:ℝ) ≤ wfun x := wc_88 x (by linarith) (by linarith)
                have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
                have hw4 : (2809593/500000000000:ℝ) ≤ wfun (y + z) := wc_448 (y + z) (by linarith) (by linarith)
                have hw5 : (870552183/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1119 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (25860883/1250000000000:ℝ) ≤ wfun x := wc_88 x (by linarith) (by linarith)
                have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
                have hw4 : (64456359/10000000000000:ℝ) ≤ wfun (y + z) := wc_458 (y + z) (by linarith) (by linarith)
                have hw5 : (1772905213/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1125 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_90 x (by linarith) (by linarith)
              have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_179 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
              have hw3 : (15728411/1250000000000:ℝ) ≤ wfun (x + y) := wc_511 (x + y) (by linarith) (by linarith)
              have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_449 (y + z) (by linarith) (by linarith)
              have hw5 : (1771842379/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1126 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
            have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_179 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
            have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_506 (x + y) (by linarith) (by linarith)
            have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_465 (y + z) (by linarith) (by linarith)
            have hw5 : (112675493/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1130 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (4297/4096:ℝ) with hc | hc
          · rcases le_total x (8619/8192:ℝ) with hc | hc
            · have hw0 : (25860883/1250000000000:ℝ) ≤ wfun x := wc_88 x (by linarith) (by linarith)
              have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
              have hw3 : (138011869/10000000000000:ℝ) ≤ wfun (x + y) := wc_514 (x + y) (by linarith) (by linarith)
              have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_465 (y + z) (by linarith) (by linarith)
              have hw5 : (180388897/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_1129 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_90 x (by linarith) (by linarith)
              have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
              have hw3 : (30150607/2000000000000:ℝ) ≤ wfun (x + y) := wc_520 (x + y) (by linarith) (by linarith)
              have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_465 (y + z) (by linarith) (by linarith)
              have hw5 : (1836199483/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1137 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
            have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
            have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_515 (x + y) (by linarith) (by linarith)
            have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_479 (y + z) (by linarith) (by linarith)
            have hw5 : (933826779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1140 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total x (4307/4096:ℝ) with hc | hc
      · rcases le_total y (8119/4096:ℝ) with hc | hc
        · rcases le_total z (4307/4096:ℝ) with hc | hc
          · rcases le_total x (8609/8192:ℝ) with hc | hc
            · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
              have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_179 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
              have hw3 : (46310863/5000000000000:ℝ) ≤ wfun (x + y) := wc_478 (x + y) (by linarith) (by linarith)
              have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_479 (y + z) (by linarith) (by linarith)
              have hw5 : (180388897/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_1129 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
              have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_179 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
              have hw3 : (25782839/2500000000000:ℝ) ≤ wfun (x + y) := wc_499 (x + y) (by linarith) (by linarith)
              have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_479 (y + z) (by linarith) (by linarith)
              have hw5 : (1836199483/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1137 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
            have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_179 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_479 (x + y) (by linarith) (by linarith)
            have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_506 (y + z) (by linarith) (by linarith)
            have hw5 : (933826779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1140 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (4307/4096:ℝ) with hc | hc
          · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
            have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_506 (x + y) (by linarith) (by linarith)
            have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_506 (y + z) (by linarith) (by linarith)
            have hw5 : (933826779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1140 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
            have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_506 (x + y) (by linarith) (by linarith)
            have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
            have hw5 : (386709691/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1145 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total y (8119/4096:ℝ) with hc | hc
        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
          have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_179 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
          have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_506 (x + y) (by linarith) (by linarith)
          have hw4 : (5774823/625000000000:ℝ) ≤ wfun (y + z) := wc_480 (y + z) (by linarith) (by linarith)
          have hw5 : (1865416811/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1141 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
          have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
          have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_515 (x + y) (by linarith) (by linarith)
          have hw4 : (569617/50000000000:ℝ) ≤ wfun (y + z) := wc_507 (y + z) (by linarith) (by linarith)
          have hw5 : (965616743/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1146 (x + y + z) (by linarith) (by linarith)
          linarith

set_option maxHeartbeats 20000000 in
lemma ch_165 (x y z : ℝ) (hx1 : (539/512:ℝ) ≤ x) (hx2 : x ≤ (17/16:ℝ))
    (hy1 : (1013/512:ℝ) ≤ y) (hy2 : y ≤ (509/256:ℝ))
    (hz1 : (539/512:ℝ) ≤ z) (hz2 : z ≤ (17/16:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (1083/1024:ℝ) with hc | hc
  · rcases le_total y (2031/1024:ℝ) with hc | hc
    · rcases le_total z (1083/1024:ℝ) with hc | hc
      · rcases le_total x (2161/2048:ℝ) with hc | hc
        · rcases le_total y (4057/2048:ℝ) with hc | hc
          · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_93 x (by linarith) (by linarith)
            have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_163 y (by linarith) (by linarith)
            have hw3 : (92247841/10000000000000:ℝ) ≤ wfun (x + y) := wc_481 (x + y) (by linarith) (by linarith)
            have hw4 : (22987523/2500000000000:ℝ) ≤ wfun (y + z) := wc_482 (y + z) (by linarith) (by linarith)
            have hw5 : (1922008203/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1149 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_93 x (by linarith) (by linarith)
            have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_180 y (by linarith) (by linarith)
            have hw3 : (13745521/1000000000000:ℝ) ≤ wfun (x + y) := wc_517 (x + y) (by linarith) (by linarith)
            have hw4 : (2140811/156250000000:ℝ) ≤ wfun (y + z) := wc_518 (y + z) (by linarith) (by linarith)
            have hw5 : (2056124169/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1165 (x + y + z) (by linarith) (by linarith)
            linarith
        · have hw1 : (200253263/500000000000:ℝ) ≤ wfun y := wc_164 y (by linarith) (by linarith)
          have hw3 : (2140811/156250000000:ℝ) ≤ wfun (x + y) := wc_518 (x + y) (by linarith) (by linarith)
          have hw4 : (11456693/1250000000000:ℝ) ≤ wfun (y + z) := wc_483 (y + z) (by linarith) (by linarith)
          have hw5 : (410242943/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1166 (x + y + z) (by linarith) (by linarith)
          linarith
      · have hw1 : (200253263/500000000000:ℝ) ≤ wfun y := wc_164 y (by linarith) (by linarith)
        have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_98 z (by linarith) (by linarith)
        have hw3 : (11456693/1250000000000:ℝ) ≤ wfun (x + y) := wc_483 (x + y) (by linarith) (by linarith)
        have hw4 : (190300253/10000000000000:ℝ) ≤ wfun (y + z) := wc_533 (y + z) (by linarith) (by linarith)
        have hw5 : (272985599/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1172 (x + y + z) (by linarith) (by linarith)
        linarith
    · rcases le_total z (1083/1024:ℝ) with hc | hc
      · rcases le_total x (2161/2048:ℝ) with hc | hc
        · rcases le_total y (4067/2048:ℝ) with hc | hc
          · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_93 x (by linarith) (by linarith)
            have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_195 y (by linarith) (by linarith)
            have hw3 : (23941523/1250000000000:ℝ) ≤ wfun (x + y) := wc_531 (x + y) (by linarith) (by linarith)
            have hw4 : (7636599/400000000000:ℝ) ≤ wfun (y + z) := wc_532 (y + z) (by linarith) (by linarith)
            have hw5 : (2194341861/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1170 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_93 x (by linarith) (by linarith)
            have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_210 y (by linarith) (by linarith)
            have hw3 : (25442213/1000000000000:ℝ) ≤ wfun (x + y) := wc_544 (x + y) (by linarith) (by linarith)
            have hw4 : (63400731/2500000000000:ℝ) ≤ wfun (y + z) := wc_545 (y + z) (by linarith) (by linarith)
            have hw5 : (2336612903/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1176 (x + y + z) (by linarith) (by linarith)
            linarith
        · have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_196 y (by linarith) (by linarith)
          have hw3 : (63400731/2500000000000:ℝ) ≤ wfun (x + y) := wc_545 (x + y) (by linarith) (by linarith)
          have hw4 : (190300253/10000000000000:ℝ) ≤ wfun (y + z) := wc_533 (y + z) (by linarith) (by linarith)
          have hw5 : (291380049/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1177 (x + y + z) (by linarith) (by linarith)
          linarith
      · have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_196 y (by linarith) (by linarith)
        have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_98 z (by linarith) (by linarith)
        have hw3 : (190300253/10000000000000:ℝ) ≤ wfun (x + y) := wc_533 (x + y) (by linarith) (by linarith)
        have hw4 : (161986357/5000000000000:ℝ) ≤ wfun (y + z) := wc_554 (y + z) (by linarith) (by linarith)
        have hw5 : (3861047/15625000000:ℝ) ≤ wfun (x + y + z) := wc_1179 (x + y + z) (by linarith) (by linarith)
        linarith
  · rcases le_total y (2031/1024:ℝ) with hc | hc
    · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_98 x (by linarith) (by linarith)
      have hw1 : (200253263/500000000000:ℝ) ≤ wfun y := wc_164 y (by linarith) (by linarith)
      have hw3 : (190300253/10000000000000:ℝ) ≤ wfun (x + y) := wc_533 (x + y) (by linarith) (by linarith)
      have hw4 : (91064031/10000000000000:ℝ) ≤ wfun (y + z) := wc_484 (y + z) (by linarith) (by linarith)
      have hw5 : (271686247/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1173 (x + y + z) (by linarith) (by linarith)
      linarith
    · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_98 x (by linarith) (by linarith)
      have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_196 y (by linarith) (by linarith)
      have hw3 : (161986357/5000000000000:ℝ) ≤ wfun (x + y) := wc_554 (x + y) (by linarith) (by linarith)
      have hw4 : (189078223/10000000000000:ℝ) ≤ wfun (y + z) := wc_534 (y + z) (by linarith) (by linarith)
      have hw5 : (1229661173/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1180 (x + y + z) (by linarith) (by linarith)
      linarith

set_option maxHeartbeats 20000000 in
lemma ch_170 (x y z : ℝ) (hx1 : (267/256:ℝ) ≤ x) (hx2 : x ≤ (539/512:ℝ))
    (hy1 : (1023/512:ℝ) ≤ y) (hy2 : y ≤ (257/128:ℝ))
    (hz1 : (131/128:ℝ) ≤ z) (hz2 : z ≤ (267/256:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total z (529/512:ℝ) with hc | hc
  · rcases le_total x (1073/1024:ℝ) with hc | hc
    · rcases le_total y (2051/1024:ℝ) with hc | hc
      · rcases le_total z (1053/1024:ℝ) with hc | hc
        · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
          have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
            rcases le_total y (2:ℝ) with hq10 | hq10
            · exact le_trans (by norm_num) (wc_233 y (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_235 y (by linarith) (by linarith))
          have hw2 : (3436255003/5000000000000:ℝ) ≤ wfun z := wc_11 z (by linarith) (by linarith)
          have hw3 : (161986357/5000000000000:ℝ) ≤ wfun (x + y) := wc_554 (x + y) (by linarith) (by linarith)
          have hw4 : (293481/2500000000000:ℝ) ≤ wfun (y + z) := wc_363 (y + z) (by linarith) (by linarith)
          have hw5 : (249365309/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_877 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
          have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
            rcases le_total y (2:ℝ) with hq10 | hq10
            · exact le_trans (by norm_num) (wc_233 y (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_235 y (by linarith) (by linarith))
          have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_15 z (by linarith) (by linarith)
          have hw3 : (161986357/5000000000000:ℝ) ≤ wfun (x + y) := wc_554 (x + y) (by linarith) (by linarith)
          have hw4 : (28474189/10000000000000:ℝ) ≤ wfun (y + z) := wc_421 (y + z) (by linarith) (by linarith)
          have hw5 : (600137957/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_929 (x + y + z) (by linarith) (by linarith)
          linarith
      · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
        have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_239 y (by linarith) (by linarith)
        have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
        have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_564 (x + y) (by linarith) (by linarith)
        have hw4 : (28290747/10000000000000:ℝ) ≤ wfun (y + z) := wc_422 (y + z) (by linarith) (by linarith)
        have hw5 : (37329233/312500000000:ℝ) ≤ wfun (x + y + z) := wc_930 (x + y + z) (by linarith) (by linarith)
        linarith
    · rcases le_total y (2051/1024:ℝ) with hc | hc
      · rcases le_total z (1053/1024:ℝ) with hc | hc
        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
          have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
            rcases le_total y (2:ℝ) with hq10 | hq10
            · exact le_trans (by norm_num) (wc_233 y (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_235 y (by linarith) (by linarith))
          have hw2 : (3436255003/5000000000000:ℝ) ≤ wfun z := wc_11 z (by linarith) (by linarith)
          have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_564 (x + y) (by linarith) (by linarith)
          have hw4 : (293481/2500000000000:ℝ) ≤ wfun (y + z) := wc_363 (y + z) (by linarith) (by linarith)
          have hw5 : (600137957/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_929 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
          have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
            rcases le_total y (2:ℝ) with hq10 | hq10
            · exact le_trans (by norm_num) (wc_233 y (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_235 y (by linarith) (by linarith))
          have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_15 z (by linarith) (by linarith)
          have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_564 (x + y) (by linarith) (by linarith)
          have hw4 : (28474189/10000000000000:ℝ) ≤ wfun (y + z) := wc_421 (y + z) (by linarith) (by linarith)
          have hw5 : (1420672477/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1017 (x + y + z) (by linarith) (by linarith)
          linarith
      · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
        have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_239 y (by linarith) (by linarith)
        have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
        have hw3 : (694482783/10000000000000:ℝ) ≤ wfun (x + y) := wc_570 (x + y) (by linarith) (by linarith)
        have hw4 : (28290747/10000000000000:ℝ) ≤ wfun (y + z) := wc_422 (y + z) (by linarith) (by linarith)
        have hw5 : (1413886087/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1018 (x + y + z) (by linarith) (by linarith)
        linarith
  · rcases le_total x (1073/1024:ℝ) with hc | hc
    · rcases le_total y (2051/1024:ℝ) with hc | hc
      · rcases le_total z (1063/1024:ℝ) with hc | hc
        · rcases le_total x (2141/2048:ℝ) with hc | hc
          · rcases le_total y (4097/2048:ℝ) with hc | hc
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
              have hw1 : (1591808227/10000000000000:ℝ) ≤ wfun y := by
                rcases le_total y (2:ℝ) with hq10 | hq10
                · exact le_trans (by norm_num) (wc_233 y (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_234 y (by linarith) (by linarith))
              have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
              have hw3 : (326066581/10000000000000:ℝ) ≤ wfun (x + y) := wc_552 (x + y) (by linarith) (by linarith)
              have hw4 : (22987523/2500000000000:ℝ) ≤ wfun (y + z) := wc_482 (y + z) (by linarith) (by linarith)
              have hw5 : (1427499659/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1015 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
              have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := wc_237 y (by linarith) (by linarith)
              have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
              have hw3 : (406405247/10000000000000:ℝ) ≤ wfun (x + y) := wc_560 (x + y) (by linarith) (by linarith)
              have hw4 : (2140811/156250000000:ℝ) ≤ wfun (y + z) := wc_518 (y + z) (by linarith) (by linarith)
              have hw5 : (1544741841/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1069 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (4097/2048:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_56 x (by linarith) (by linarith)
              have hw1 : (1591808227/10000000000000:ℝ) ≤ wfun y := by
                rcases le_total y (2:ℝ) with hq10 | hq10
                · exact le_trans (by norm_num) (wc_233 y (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_234 y (by linarith) (by linarith))
              have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
              have hw3 : (406405247/10000000000000:ℝ) ≤ wfun (x + y) := wc_560 (x + y) (by linarith) (by linarith)
              have hw4 : (22987523/2500000000000:ℝ) ≤ wfun (y + z) := wc_482 (y + z) (by linarith) (by linarith)
              have hw5 : (1544741841/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1069 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_56 x (by linarith) (by linarith)
              have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := wc_237 y (by linarith) (by linarith)
              have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
              have hw3 : (495376037/10000000000000:ℝ) ≤ wfun (x + y) := wc_562 (x + y) (by linarith) (by linarith)
              have hw4 : (2140811/156250000000:ℝ) ≤ wfun (y + z) := wc_518 (y + z) (by linarith) (by linarith)
              have hw5 : (1666270777/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1106 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (2141/2048:ℝ) with hc | hc
          · rcases le_total y (4097/2048:ℝ) with hc | hc
            · rcases le_total z (2131/2048:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                have hw1 : (1591808227/10000000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (2:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_233 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_234 y (by linarith) (by linarith))
                have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                have hw3 : (326066581/10000000000000:ℝ) ≤ wfun (x + y) := wc_552 (x + y) (by linarith) (by linarith)
                have hw4 : (23941523/1250000000000:ℝ) ≤ wfun (y + z) := wc_531 (y + z) (by linarith) (by linarith)
                have hw5 : (1670268489/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1105 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                have hw1 : (1591808227/10000000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (2:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_233 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_234 y (by linarith) (by linarith))
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                have hw3 : (326066581/10000000000000:ℝ) ≤ wfun (x + y) := wc_552 (x + y) (by linarith) (by linarith)
                have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_544 (y + z) (by linarith) (by linarith)
                have hw5 : (1796338383/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1133 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (2131/2048:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := wc_237 y (by linarith) (by linarith)
                have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                have hw3 : (406405247/10000000000000:ℝ) ≤ wfun (x + y) := wc_560 (x + y) (by linarith) (by linarith)
                have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_544 (y + z) (by linarith) (by linarith)
                have hw5 : (1796338383/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1133 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := wc_237 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                have hw3 : (406405247/10000000000000:ℝ) ≤ wfun (x + y) := wc_560 (x + y) (by linarith) (by linarith)
                have hw4 : (326066581/10000000000000:ℝ) ≤ wfun (y + z) := wc_552 (y + z) (by linarith) (by linarith)
                have hw5 : (963306969/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1148 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (4097/2048:ℝ) with hc | hc
            · rcases le_total z (2131/2048:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_56 x (by linarith) (by linarith)
                have hw1 : (1591808227/10000000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (2:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_233 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_234 y (by linarith) (by linarith))
                have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                have hw3 : (406405247/10000000000000:ℝ) ≤ wfun (x + y) := wc_560 (x + y) (by linarith) (by linarith)
                have hw4 : (23941523/1250000000000:ℝ) ≤ wfun (y + z) := wc_531 (y + z) (by linarith) (by linarith)
                have hw5 : (1796338383/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1133 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_56 x (by linarith) (by linarith)
                have hw1 : (1591808227/10000000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (2:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_233 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_234 y (by linarith) (by linarith))
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                have hw3 : (406405247/10000000000000:ℝ) ≤ wfun (x + y) := wc_560 (x + y) (by linarith) (by linarith)
                have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_544 (y + z) (by linarith) (by linarith)
                have hw5 : (963306969/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1148 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_56 x (by linarith) (by linarith)
              have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := wc_237 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
              have hw3 : (495376037/10000000000000:ℝ) ≤ wfun (x + y) := wc_562 (x + y) (by linarith) (by linarith)
              have hw4 : (63400731/2500000000000:ℝ) ≤ wfun (y + z) := wc_545 (y + z) (by linarith) (by linarith)
              have hw5 : (1922008203/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1149 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (1063/1024:ℝ) with hc | hc
        · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
          have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_239 y (by linarith) (by linarith)
          have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
          have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_564 (x + y) (by linarith) (by linarith)
          have hw4 : (190300253/10000000000000:ℝ) ≤ wfun (y + z) := wc_533 (y + z) (by linarith) (by linarith)
          have hw5 : (1658311191/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1108 (x + y + z) (by linarith) (by linarith)
          linarith
        · rcases le_total x (2141/2048:ℝ) with hc | hc
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
            have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_239 y (by linarith) (by linarith)
            have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
            have hw3 : (493784853/10000000000000:ℝ) ≤ wfun (x + y) := wc_563 (x + y) (by linarith) (by linarith)
            have hw4 : (161986357/5000000000000:ℝ) ≤ wfun (y + z) := wc_554 (y + z) (by linarith) (by linarith)
            have hw5 : (1917416231/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1150 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_56 x (by linarith) (by linarith)
            have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_239 y (by linarith) (by linarith)
            have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
            have hw3 : (295506067/5000000000000:ℝ) ≤ wfun (x + y) := wc_567 (x + y) (by linarith) (by linarith)
            have hw4 : (161986357/5000000000000:ℝ) ≤ wfun (y + z) := wc_554 (y + z) (by linarith) (by linarith)
            have hw5 : (410242943/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1166 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total y (2051/1024:ℝ) with hc | hc
      · rcases le_total z (1063/1024:ℝ) with hc | hc
        · rcases le_total x (2151/2048:ℝ) with hc | hc
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
            have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
              rcases le_total y (2:ℝ) with hq10 | hq10
              · exact le_trans (by norm_num) (wc_233 y (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_235 y (by linarith) (by linarith))
            have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
            have hw3 : (493784853/10000000000000:ℝ) ≤ wfun (x + y) := wc_563 (x + y) (by linarith) (by linarith)
            have hw4 : (11456693/1250000000000:ℝ) ≤ wfun (y + z) := wc_483 (y + z) (by linarith) (by linarith)
            have hw5 : (66491401/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1107 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
            have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
              rcases le_total y (2:ℝ) with hq10 | hq10
              · exact le_trans (by norm_num) (wc_233 y (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_235 y (by linarith) (by linarith))
            have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
            have hw3 : (295506067/5000000000000:ℝ) ≤ wfun (x + y) := wc_567 (x + y) (by linarith) (by linarith)
            have hw4 : (11456693/1250000000000:ℝ) ≤ wfun (y + z) := wc_483 (y + z) (by linarith) (by linarith)
            have hw5 : (1787757479/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1135 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total x (2151/2048:ℝ) with hc | hc
          · rcases le_total y (4097/2048:ℝ) with hc | hc
            · rcases le_total z (2131/2048:ℝ) with hc | hc
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
                have hw1 : (1591808227/10000000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (2:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_233 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_234 y (by linarith) (by linarith))
                have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                have hw3 : (495376037/10000000000000:ℝ) ≤ wfun (x + y) := wc_562 (x + y) (by linarith) (by linarith)
                have hw4 : (23941523/1250000000000:ℝ) ≤ wfun (y + z) := wc_531 (y + z) (by linarith) (by linarith)
                have hw5 : (963306969/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1148 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
                have hw1 : (1591808227/10000000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (2:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_233 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_234 y (by linarith) (by linarith))
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                have hw3 : (495376037/10000000000000:ℝ) ≤ wfun (x + y) := wc_562 (x + y) (by linarith) (by linarith)
                have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_544 (y + z) (by linarith) (by linarith)
                have hw5 : (2061048329/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1164 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
              have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := wc_237 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
              have hw3 : (148228771/2500000000000:ℝ) ≤ wfun (x + y) := wc_566 (x + y) (by linarith) (by linarith)
              have hw4 : (63400731/2500000000000:ℝ) ≤ wfun (y + z) := wc_545 (y + z) (by linarith) (by linarith)
              have hw5 : (2056124169/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1165 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
            have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
              rcases le_total y (2:ℝ) with hq10 | hq10
              · exact le_trans (by norm_num) (wc_233 y (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_235 y (by linarith) (by linarith))
            have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
            have hw3 : (295506067/5000000000000:ℝ) ≤ wfun (x + y) := wc_567 (x + y) (by linarith) (by linarith)
            have hw4 : (190300253/10000000000000:ℝ) ≤ wfun (y + z) := wc_533 (y + z) (by linarith) (by linarith)
            have hw5 : (410242943/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1166 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total z (1063/1024:ℝ) with hc | hc
        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
          have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_239 y (by linarith) (by linarith)
          have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
          have hw3 : (694482783/10000000000000:ℝ) ≤ wfun (x + y) := wc_570 (x + y) (by linarith) (by linarith)
          have hw4 : (190300253/10000000000000:ℝ) ≤ wfun (y + z) := wc_533 (y + z) (by linarith) (by linarith)
          have hw5 : (1912837973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1151 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
          have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_239 y (by linarith) (by linarith)
          have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
          have hw3 : (694482783/10000000000000:ℝ) ≤ wfun (x + y) := wc_570 (x + y) (by linarith) (by linarith)
          have hw4 : (161986357/5000000000000:ℝ) ≤ wfun (y + z) := wc_554 (y + z) (by linarith) (by linarith)
          have hw5 : (272985599/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1172 (x + y + z) (by linarith) (by linarith)
          linarith

set_option maxHeartbeats 20000000 in
lemma ch_195 (x y z : ℝ) (hx1 : (63/64:ℝ) ≤ x) (hx2 : x ≤ (73/64:ℝ))
    (hy1 : (131/64:ℝ) ≤ y) (hy2 : y ≤ (141/64:ℝ))
    (hz1 : (121/64:ℝ) ≤ z) (hz2 : z ≤ (141/64:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
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
        · have hw1 : (42177537/1000000000000:ℝ) ≤ wfun y := wc_257 y (by linarith) (by linarith)
          have hw2 : (795663039/1250000000000:ℝ) ≤ wfun z := wc_117 z (by linarith) (by linarith)
          have hw3 : (75856633/10000000000000:ℝ) ≤ wfun (x + y) := wc_492 (x + y) (by linarith) (by linarith)
          linarith
        · rcases le_total x (131/128:ℝ) with hc | hc
          · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := by
              rcases le_total x (1:ℝ) with hq00 | hq00
              · exact le_trans (by norm_num) (wc_5 x (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_7 x (by linarith) (by linarith))
            have hw1 : (42177537/1000000000000:ℝ) ≤ wfun y := wc_257 y (by linarith) (by linarith)
            have hw3 : (79711817/10000000000000:ℝ) ≤ wfun (x + y) := wc_491 (x + y) (by linarith) (by linarith)
            have hw4 : (56143/10000000000000:ℝ) ≤ wfun (y + z) := wc_708 (y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total y (267/128:ℝ) with hc | hc
            · rcases le_total z (257/128:ℝ) with hc | hc
              · rcases le_total x (267/256:ℝ) with hc | hc
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
                  have hw1 : (18186303/400000000000:ℝ) ≤ wfun y := wc_255 y (by linarith) (by linarith)
                  have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                    rcases le_total z (2:ℝ) with hq20 | hq20
                    · exact le_trans (by norm_num) (wc_134 z (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                  have hw3 : (215107179/1250000000000:ℝ) ≤ wfun (x + y) := wc_591 (x + y) (by linarith) (by linarith)
                  have hw4 : (60567/10000000000000:ℝ) ≤ wfun (y + z) := wc_705 (y + z) (by linarith) (by linarith)
                  have hw5 : (90750063/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1271 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw1 : (18186303/400000000000:ℝ) ≤ wfun y := wc_255 y (by linarith) (by linarith)
                  have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                    rcases le_total z (2:ℝ) with hq20 | hq20
                    · exact le_trans (by norm_num) (wc_134 z (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                  have hw3 : (1629257293/5000000000000:ℝ) ≤ wfun (x + y) := wc_599 (x + y) (by linarith) (by linarith)
                  have hw4 : (60567/10000000000000:ℝ) ≤ wfun (y + z) := wc_705 (y + z) (by linarith) (by linarith)
                  have hw5 : (534939039/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1374 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw1 : (18186303/400000000000:ℝ) ≤ wfun y := wc_255 y (by linarith) (by linarith)
                have hw3 : (419583999/2500000000000:ℝ) ≤ wfun (x + y) := wc_592 (x + y) (by linarith) (by linarith)
                have hw4 : (24278963/400000000000:ℝ) ≤ wfun (y + z) := wc_830 (y + z) (by linarith) (by linarith)
                have hw5 : (1048517003/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1474 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw1 : (4789633321/10000000000000:ℝ) ≤ wfun y := wc_272 y (by linarith) (by linarith)
              have hw3 : (5096134953/10000000000000:ℝ) ≤ wfun (x + y) := wc_604 (x + y) (by linarith) (by linarith)
              have hw4 : (913271/15625000000:ℝ) ≤ wfun (y + z) := wc_832 (y + z) (by linarith) (by linarith)
              have hw5 : (1017509707/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1475 (x + y + z) (by linarith) (by linarith)
              linarith
      · have hw1 : (48584483/40000000000:ℝ) ≤ wfun y := wc_278 y (by linarith) (by linarith)
        have hw3 : (589186081/1250000000000:ℝ) ≤ wfun (x + y) := by
          rcases le_total (x + y) (13/4:ℝ) with hq30 | hq30
          · exact le_trans (by norm_num) (wc_606 (x + y) (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_609 (x + y) (by linarith) (by linarith))
        have hw4 : (13029/2500000000000:ℝ) ≤ wfun (y + z) := wc_709 (y + z) (by linarith) (by linarith)
        linarith
    · have hw0 : (15429929/1000000000000:ℝ) ≤ wfun x := wc_104 x (by linarith) (by linarith)
      have hw1 : (182240171/5000000000000:ℝ) ≤ wfun y := wc_259 y (by linarith) (by linarith)
      have hw3 : (589186081/1250000000000:ℝ) ≤ wfun (x + y) := by
        rcases le_total (x + y) (13/4:ℝ) with hq30 | hq30
        · exact le_trans (by norm_num) (wc_606 (x + y) (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_612 (x + y) (by linarith) (by linarith))
      linarith
  · have hw1 : (182240171/5000000000000:ℝ) ≤ wfun y := wc_259 y (by linarith) (by linarith)
    have hw2 : (182240171/5000000000000:ℝ) ≤ wfun z := wc_259 z (by linarith) (by linarith)
    have hw3 : (17540223/2500000000000:ℝ) ≤ wfun (x + y) := by
      rcases le_total (x + y) (13/4:ℝ) with hq30 | hq30
      · exact le_trans (by norm_num) (wc_493 (x + y) (by linarith) (by linarith))
      exact le_trans (by norm_num) (wc_612 (x + y) (by linarith) (by linarith))
    have hw4 : (2156990541/10000000000000:ℝ) ≤ wfun (y + z) := by
      rcases le_total (y + z) (17/4:ℝ) with hq40 | hq40
      · exact le_trans (by norm_num) (wc_1188 (y + z) (by linarith) (by linarith))
      exact le_trans (by norm_num) (wc_1205 (y + z) (by linarith) (by linarith))
    have hw5 : (502714163/5000000000000:ℝ) ≤ wfun (x + y + z) := by
      rcases le_total (x + y + z) (21/4:ℝ) with hq50 | hq50
      · exact le_trans (by norm_num) (wc_1476 (x + y + z) (by linarith) (by linarith))
      rcases le_total (x + y + z) (11/2:ℝ) with hq51 | hq51
      · exact le_trans (by norm_num) (wc_1513 (x + y + z) (by linarith) (by linarith))
      exact le_trans (by norm_num) (wc_1514 (x + y + z) (by linarith) (by linarith))
    linarith

set_option maxHeartbeats 20000000 in
lemma ch_204 (x y z : ℝ) (hx1 : (267/256:ℝ) ≤ x) (hx2 : x ≤ (17/16:ℝ))
    (hy1 : (6069/2048:ℝ) ≤ y) (hy2 : y ≤ (1525/512:ℝ))
    (hz1 : (267/256:ℝ) ≤ z) (hz2 : z ≤ (17/16:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (539/512:ℝ) with hc | hc
  · rcases le_total z (539/512:ℝ) with hc | hc
    · rcases le_total y (12169/4096:ℝ) with hc | hc
      · rcases le_total x (1073/1024:ℝ) with hc | hc
        · rcases le_total z (1073/1024:ℝ) with hc | hc
          · rcases le_total y (24307/8192:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (2229636307/10000000000000:ℝ) ≤ wfun y := wc_306 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
              have hw3 : (5269/2500000000000:ℝ) ≤ wfun (x + y) := wc_695 (x + y) (by linarith) (by linarith)
              have hw4 : (5269/2500000000000:ℝ) ≤ wfun (y + z) := wc_695 (y + z) (by linarith) (by linarith)
              have hw5 : (367971747/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1317 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (240095521/1250000000000:ℝ) ≤ wfun y := wc_309 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
              have hw5 : (222870971/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1334 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (24307/8192:ℝ) with hc | hc
            · rcases le_total x (2141/2048:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                have hw1 : (2229636307/10000000000000:ℝ) ≤ wfun y := wc_306 y (by linarith) (by linarith)
                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
                have hw3 : (1531809/5000000000000:ℝ) ≤ wfun (x + y) := wc_694 (x + y) (by linarith) (by linarith)
                have hw5 : (235288201/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1346 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_56 x (by linarith) (by linarith)
                have hw1 : (2229636307/10000000000000:ℝ) ≤ wfun y := wc_306 y (by linarith) (by linarith)
                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
                have hw3 : (5269/2500000000000:ℝ) ≤ wfun (x + y) := wc_697 (x + y) (by linarith) (by linarith)
                have hw5 : (26300467/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1358 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (2141/2048:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                have hw1 : (240095521/1250000000000:ℝ) ≤ wfun y := wc_309 y (by linarith) (by linarith)
                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
                have hw5 : (278880729/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1363 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_56 x (by linarith) (by linarith)
                have hw1 : (240095521/1250000000000:ℝ) ≤ wfun y := wc_309 y (by linarith) (by linarith)
                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
                have hw5 : (38610999/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1384 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (1073/1024:ℝ) with hc | hc
          · rcases le_total y (24307/8192:ℝ) with hc | hc
            · rcases le_total x (2151/2048:ℝ) with hc | hc
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
                have hw1 : (2229636307/10000000000000:ℝ) ≤ wfun y := wc_306 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw4 : (5269/2500000000000:ℝ) ≤ wfun (y + z) := wc_695 (y + z) (by linarith) (by linarith)
                have hw5 : (235288201/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1346 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
                have hw1 : (2229636307/10000000000000:ℝ) ≤ wfun y := wc_306 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw4 : (5269/2500000000000:ℝ) ≤ wfun (y + z) := wc_695 (y + z) (by linarith) (by linarith)
                have hw5 : (26300467/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1358 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (2151/2048:ℝ) with hc | hc
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
                have hw1 : (240095521/1250000000000:ℝ) ≤ wfun y := wc_309 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw5 : (278880729/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1363 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
                have hw1 : (240095521/1250000000000:ℝ) ≤ wfun y := wc_309 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (2112593/10000000000000:ℝ) ≤ wfun (x + y) := wc_719 (x + y) (by linarith) (by linarith)
                have hw5 : (38610999/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1384 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (24307/8192:ℝ) with hc | hc
            · rcases le_total x (2151/2048:ℝ) with hc | hc
              · rcases le_total z (2151/2048:ℝ) with hc | hc
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
                  have hw1 : (2229636307/10000000000000:ℝ) ≤ wfun y := wc_306 y (by linarith) (by linarith)
                  have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
                  have hw5 : (23421341/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1375 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
                  have hw1 : (2229636307/10000000000000:ℝ) ≤ wfun y := wc_306 y (by linarith) (by linarith)
                  have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
                  have hw5 : (646985877/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1391 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (2151/2048:ℝ) with hc | hc
                · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
                  have hw1 : (2229636307/10000000000000:ℝ) ≤ wfun y := wc_306 y (by linarith) (by linarith)
                  have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
                  have hw5 : (646985877/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1391 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
                  have hw1 : (2229636307/10000000000000:ℝ) ≤ wfun y := wc_306 y (by linarith) (by linarith)
                  have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
                  have hw5 : (711359973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1404 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total x (2151/2048:ℝ) with hc | hc
              · rcases le_total z (2151/2048:ℝ) with hc | hc
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
                  have hw1 : (240095521/1250000000000:ℝ) ≤ wfun y := wc_309 y (by linarith) (by linarith)
                  have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
                  have hw5 : (682031579/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1395 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
                  have hw1 : (240095521/1250000000000:ℝ) ≤ wfun y := wc_309 y (by linarith) (by linarith)
                  have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
                  have hw4 : (2112593/10000000000000:ℝ) ≤ wfun (y + z) := wc_719 (y + z) (by linarith) (by linarith)
                  have hw5 : (187000619/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1416 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (2151/2048:ℝ) with hc | hc
                · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
                  have hw1 : (240095521/1250000000000:ℝ) ≤ wfun y := wc_309 y (by linarith) (by linarith)
                  have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
                  have hw3 : (2112593/10000000000000:ℝ) ≤ wfun (x + y) := wc_719 (x + y) (by linarith) (by linarith)
                  have hw5 : (187000619/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1416 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
                  have hw1 : (240095521/1250000000000:ℝ) ≤ wfun y := wc_309 y (by linarith) (by linarith)
                  have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
                  have hw3 : (2112593/10000000000000:ℝ) ≤ wfun (x + y) := wc_719 (x + y) (by linarith) (by linarith)
                  have hw4 : (2112593/10000000000000:ℝ) ≤ wfun (y + z) := wc_719 (y + z) (by linarith) (by linarith)
                  have hw5 : (816857769/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1426 (x + y + z) (by linarith) (by linarith)
                  linarith
      · rcases le_total x (1073/1024:ℝ) with hc | hc
        · rcases le_total z (1073/1024:ℝ) with hc | hc
          · rcases le_total y (24369/8192:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (1635115293/10000000000000:ℝ) ≤ wfun y := wc_310 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
              have hw5 : (66336319/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1359 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (686336349/5000000000000:ℝ) ≤ wfun y := wc_313 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
              have hw3 : (1298021/5000000000000:ℝ) ≤ wfun (x + y) := wc_721 (x + y) (by linarith) (by linarith)
              have hw4 : (1298021/5000000000000:ℝ) ≤ wfun (y + z) := wc_721 (y + z) (by linarith) (by linarith)
              have hw5 : (77842061/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1385 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (24369/8192:ℝ) with hc | hc
            · rcases le_total x (2141/2048:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                have hw1 : (1635115293/10000000000000:ℝ) ≤ wfun y := wc_310 y (by linarith) (by linarith)
                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
                have hw4 : (21693/40000000000:ℝ) ≤ wfun (y + z) := wc_725 (y + z) (by linarith) (by linarith)
                have hw5 : (652032997/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1392 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_56 x (by linarith) (by linarith)
                have hw1 : (1635115293/10000000000000:ℝ) ≤ wfun y := wc_310 y (by linarith) (by linarith)
                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
                have hw3 : (539537/10000000000000:ℝ) ≤ wfun (x + y) := wc_715 (x + y) (by linarith) (by linarith)
                have hw4 : (21693/40000000000:ℝ) ≤ wfun (y + z) := wc_725 (y + z) (by linarith) (by linarith)
                have hw5 : (71657399/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_1407 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (2141/2048:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                have hw1 : (686336349/5000000000000:ℝ) ≤ wfun y := wc_313 y (by linarith) (by linarith)
                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
                have hw3 : (2602367/10000000000000:ℝ) ≤ wfun (x + y) := wc_720 (x + y) (by linarith) (by linarith)
                have hw4 : (11506103/5000000000000:ℝ) ≤ wfun (y + z) := wc_746 (y + z) (by linarith) (by linarith)
                have hw5 : (753304927/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1417 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_56 x (by linarith) (by linarith)
                have hw1 : (686336349/5000000000000:ℝ) ≤ wfun y := wc_313 y (by linarith) (by linarith)
                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
                have hw3 : (10298543/10000000000000:ℝ) ≤ wfun (x + y) := wc_732 (x + y) (by linarith) (by linarith)
                have hw4 : (11506103/5000000000000:ℝ) ≤ wfun (y + z) := wc_746 (y + z) (by linarith) (by linarith)
                have hw5 : (51394681/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1428 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (1073/1024:ℝ) with hc | hc
          · rcases le_total y (24369/8192:ℝ) with hc | hc
            · rcases le_total x (2151/2048:ℝ) with hc | hc
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
                have hw1 : (1635115293/10000000000000:ℝ) ≤ wfun y := wc_310 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (2718231/5000000000000:ℝ) ≤ wfun (x + y) := wc_724 (x + y) (by linarith) (by linarith)
                have hw5 : (652032997/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1392 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
                have hw1 : (1635115293/10000000000000:ℝ) ≤ wfun y := wc_310 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (15418319/10000000000000:ℝ) ≤ wfun (x + y) := wc_737 (x + y) (by linarith) (by linarith)
                have hw5 : (71657399/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_1407 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (2151/2048:ℝ) with hc | hc
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
                have hw1 : (686336349/5000000000000:ℝ) ≤ wfun y := wc_313 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (5767053/2500000000000:ℝ) ≤ wfun (x + y) := wc_745 (x + y) (by linarith) (by linarith)
                have hw4 : (1298021/5000000000000:ℝ) ≤ wfun (y + z) := wc_721 (y + z) (by linarith) (by linarith)
                have hw5 : (753304927/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1417 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
                have hw1 : (686336349/5000000000000:ℝ) ≤ wfun y := wc_313 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (20444851/5000000000000:ℝ) ≤ wfun (x + y) := wc_754 (x + y) (by linarith) (by linarith)
                have hw4 : (1298021/5000000000000:ℝ) ≤ wfun (y + z) := wc_721 (y + z) (by linarith) (by linarith)
                have hw5 : (51394681/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1428 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (24369/8192:ℝ) with hc | hc
            · rcases le_total x (2151/2048:ℝ) with hc | hc
              · rcases le_total z (2151/2048:ℝ) with hc | hc
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
                  have hw1 : (1635115293/10000000000000:ℝ) ≤ wfun y := wc_310 y (by linarith) (by linarith)
                  have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
                  have hw3 : (2718231/5000000000000:ℝ) ≤ wfun (x + y) := wc_724 (x + y) (by linarith) (by linarith)
                  have hw4 : (2718231/5000000000000:ℝ) ≤ wfun (y + z) := wc_724 (y + z) (by linarith) (by linarith)
                  have hw5 : (785517521/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1423 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
                  have hw1 : (1635115293/10000000000000:ℝ) ≤ wfun y := wc_310 y (by linarith) (by linarith)
                  have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
                  have hw3 : (2718231/5000000000000:ℝ) ≤ wfun (x + y) := wc_724 (x + y) (by linarith) (by linarith)
                  have hw4 : (15418319/10000000000000:ℝ) ≤ wfun (y + z) := wc_737 (y + z) (by linarith) (by linarith)
                  have hw5 : (42797433/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1440 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
                have hw1 : (1635115293/10000000000000:ℝ) ≤ wfun y := wc_310 y (by linarith) (by linarith)
                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
                have hw3 : (15418319/10000000000000:ℝ) ≤ wfun (x + y) := wc_737 (x + y) (by linarith) (by linarith)
                have hw4 : (21693/40000000000:ℝ) ≤ wfun (y + z) := wc_725 (y + z) (by linarith) (by linarith)
                have hw5 : (85430123/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_1441 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (2151/2048:ℝ) with hc | hc
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
                have hw1 : (686336349/5000000000000:ℝ) ≤ wfun y := wc_313 y (by linarith) (by linarith)
                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
                have hw3 : (5767053/2500000000000:ℝ) ≤ wfun (x + y) := wc_745 (x + y) (by linarith) (by linarith)
                have hw4 : (11506103/5000000000000:ℝ) ≤ wfun (y + z) := wc_746 (y + z) (by linarith) (by linarith)
                have hw5 : (894176473/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1446 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
                have hw1 : (686336349/5000000000000:ℝ) ≤ wfun y := wc_313 y (by linarith) (by linarith)
                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
                have hw3 : (20444851/5000000000000:ℝ) ≤ wfun (x + y) := wc_754 (x + y) (by linarith) (by linarith)
                have hw4 : (11506103/5000000000000:ℝ) ≤ wfun (y + z) := wc_746 (y + z) (by linarith) (by linarith)
                have hw5 : (484432071/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1453 (x + y + z) (by linarith) (by linarith)
                linarith
    · rcases le_total y (12169/4096:ℝ) with hc | hc
      · rcases le_total x (1073/1024:ℝ) with hc | hc
        · rcases le_total z (1083/1024:ℝ) with hc | hc
          · rcases le_total y (24307/8192:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (2229636307/10000000000000:ℝ) ≤ wfun y := wc_306 y (by linarith) (by linarith)
              have hw3 : (5269/2500000000000:ℝ) ≤ wfun (x + y) := wc_695 (x + y) (by linarith) (by linarith)
              have hw4 : (32949/1000000000000:ℝ) ≤ wfun (y + z) := wc_711 (y + z) (by linarith) (by linarith)
              have hw5 : (11665557/200000000000:ℝ) ≤ wfun (x + y + z) := wc_1376 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (240095521/1250000000000:ℝ) ≤ wfun y := wc_309 y (by linarith) (by linarith)
              have hw4 : (2319419/2500000000000:ℝ) ≤ wfun (y + z) := wc_731 (y + z) (by linarith) (by linarith)
              have hw5 : (5435249/80000000000:ℝ) ≤ wfun (x + y + z) := wc_1396 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
            have hw1 : (239478321/1250000000000:ℝ) ≤ wfun y := wc_307 y (by linarith) (by linarith)
            have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_98 z (by linarith) (by linarith)
            have hw4 : (3526053/2500000000000:ℝ) ≤ wfun (y + z) := wc_736 (y + z) (by linarith) (by linarith)
            have hw5 : (706509509/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1406 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (1083/1024:ℝ) with hc | hc
          · rcases le_total y (24307/8192:ℝ) with hc | hc
            · rcases le_total x (2151/2048:ℝ) with hc | hc
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
                have hw1 : (2229636307/10000000000000:ℝ) ≤ wfun y := wc_306 y (by linarith) (by linarith)
                have hw4 : (32949/1000000000000:ℝ) ≤ wfun (y + z) := wc_711 (y + z) (by linarith) (by linarith)
                have hw5 : (709989443/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1405 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
                have hw1 : (2229636307/10000000000000:ℝ) ≤ wfun y := wc_306 y (by linarith) (by linarith)
                have hw4 : (32949/1000000000000:ℝ) ≤ wfun (y + z) := wc_711 (y + z) (by linarith) (by linarith)
                have hw5 : (388566237/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1422 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (2151/2048:ℝ) with hc | hc
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
                have hw1 : (240095521/1250000000000:ℝ) ≤ wfun y := wc_309 y (by linarith) (by linarith)
                have hw4 : (2319419/2500000000000:ℝ) ≤ wfun (y + z) := wc_731 (y + z) (by linarith) (by linarith)
                have hw5 : (815285161/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1427 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
                have hw1 : (240095521/1250000000000:ℝ) ≤ wfun y := wc_309 y (by linarith) (by linarith)
                have hw3 : (2112593/10000000000000:ℝ) ≤ wfun (x + y) := wc_719 (x + y) (by linarith) (by linarith)
                have hw4 : (2319419/2500000000000:ℝ) ≤ wfun (y + z) := wc_731 (y + z) (by linarith) (by linarith)
                have hw5 : (177372543/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1445 (x + y + z) (by linarith) (by linarith)
                linarith
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
            have hw1 : (239478321/1250000000000:ℝ) ≤ wfun y := wc_307 y (by linarith) (by linarith)
            have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_98 z (by linarith) (by linarith)
            have hw4 : (3526053/2500000000000:ℝ) ≤ wfun (y + z) := wc_736 (y + z) (by linarith) (by linarith)
            have hw5 : (168599037/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1438 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total x (1073/1024:ℝ) with hc | hc
        · rcases le_total z (1083/1024:ℝ) with hc | hc
          · rcases le_total y (24369/8192:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (1635115293/10000000000000:ℝ) ≤ wfun y := wc_310 y (by linarith) (by linarith)
              have hw4 : (6078023/2000000000000:ℝ) ≤ wfun (y + z) := wc_751 (y + z) (by linarith) (by linarith)
              have hw5 : (782495959/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1424 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (686336349/5000000000000:ℝ) ≤ wfun y := wc_313 y (by linarith) (by linarith)
              have hw3 : (1298021/5000000000000:ℝ) ≤ wfun (x + y) := wc_721 (x + y) (by linarith) (by linarith)
              have hw4 : (63585659/10000000000000:ℝ) ≤ wfun (y + z) := wc_767 (y + z) (by linarith) (by linarith)
              have hw5 : (55778547/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1447 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
            have hw1 : (136952521/1000000000000:ℝ) ≤ wfun y := wc_311 y (by linarith) (by linarith)
            have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_98 z (by linarith) (by linarith)
            have hw4 : (75190749/10000000000000:ℝ) ≤ wfun (y + z) := wc_768 (y + z) (by linarith) (by linarith)
            have hw5 : (461449393/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1449 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (1083/1024:ℝ) with hc | hc
          · rcases le_total y (24369/8192:ℝ) with hc | hc
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
              have hw1 : (1635115293/10000000000000:ℝ) ≤ wfun y := wc_310 y (by linarith) (by linarith)
              have hw3 : (21693/40000000000:ℝ) ≤ wfun (x + y) := wc_725 (x + y) (by linarith) (by linarith)
              have hw4 : (6078023/2000000000000:ℝ) ≤ wfun (y + z) := wc_751 (y + z) (by linarith) (by linarith)
              have hw5 : (925654441/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1448 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
              have hw1 : (686336349/5000000000000:ℝ) ≤ wfun y := wc_313 y (by linarith) (by linarith)
              have hw3 : (11506103/5000000000000:ℝ) ≤ wfun (x + y) := wc_746 (x + y) (by linarith) (by linarith)
              have hw4 : (63585659/10000000000000:ℝ) ≤ wfun (y + z) := wc_767 (y + z) (by linarith) (by linarith)
              have hw5 : (1044341323/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1465 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
            have hw1 : (136952521/1000000000000:ℝ) ≤ wfun y := wc_311 y (by linarith) (by linarith)
            have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_98 z (by linarith) (by linarith)
            have hw3 : (1350713/2500000000000:ℝ) ≤ wfun (x + y) := wc_726 (x + y) (by linarith) (by linarith)
            have hw4 : (75190749/10000000000000:ℝ) ≤ wfun (y + z) := wc_768 (y + z) (by linarith) (by linarith)
            have hw5 : (215367333/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1466 (x + y + z) (by linarith) (by linarith)
            linarith
  · rcases le_total z (539/512:ℝ) with hc | hc
    · rcases le_total y (12169/4096:ℝ) with hc | hc
      · rcases le_total x (1083/1024:ℝ) with hc | hc
        · rcases le_total z (1073/1024:ℝ) with hc | hc
          · rcases le_total y (24307/8192:ℝ) with hc | hc
            · have hw1 : (2229636307/10000000000000:ℝ) ≤ wfun y := wc_306 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
              have hw3 : (32949/1000000000000:ℝ) ≤ wfun (x + y) := wc_711 (x + y) (by linarith) (by linarith)
              have hw4 : (5269/2500000000000:ℝ) ≤ wfun (y + z) := wc_695 (y + z) (by linarith) (by linarith)
              have hw5 : (11665557/200000000000:ℝ) ≤ wfun (x + y + z) := wc_1376 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw1 : (240095521/1250000000000:ℝ) ≤ wfun y := wc_309 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
              have hw3 : (2319419/2500000000000:ℝ) ≤ wfun (x + y) := wc_731 (x + y) (by linarith) (by linarith)
              have hw5 : (5435249/80000000000:ℝ) ≤ wfun (x + y + z) := wc_1396 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (24307/8192:ℝ) with hc | hc
            · rcases le_total x (2161/2048:ℝ) with hc | hc
              · rcases le_total z (2151/2048:ℝ) with hc | hc
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_93 x (by linarith) (by linarith)
                  have hw1 : (2229636307/10000000000000:ℝ) ≤ wfun y := wc_306 y (by linarith) (by linarith)
                  have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
                  have hw3 : (330293/10000000000000:ℝ) ≤ wfun (x + y) := wc_710 (x + y) (by linarith) (by linarith)
                  have hw5 : (711359973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1404 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_93 x (by linarith) (by linarith)
                  have hw1 : (2229636307/10000000000000:ℝ) ≤ wfun y := wc_306 y (by linarith) (by linarith)
                  have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
                  have hw3 : (330293/10000000000000:ℝ) ≤ wfun (x + y) := wc_710 (x + y) (by linarith) (by linarith)
                  have hw5 : (778631889/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1421 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw1 : (2229636307/10000000000000:ℝ) ≤ wfun y := wc_306 y (by linarith) (by linarith)
                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
                have hw3 : (471761/1000000000000:ℝ) ≤ wfun (x + y) := wc_723 (x + y) (by linarith) (by linarith)
                have hw5 : (388566237/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1422 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (2161/2048:ℝ) with hc | hc
              · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_93 x (by linarith) (by linarith)
                have hw1 : (240095521/1250000000000:ℝ) ≤ wfun y := wc_309 y (by linarith) (by linarith)
                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
                have hw3 : (930027/1000000000000:ℝ) ≤ wfun (x + y) := wc_730 (x + y) (by linarith) (by linarith)
                have hw5 : (815285161/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1427 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw1 : (240095521/1250000000000:ℝ) ≤ wfun y := wc_309 y (by linarith) (by linarith)
                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
                have hw3 : (21563547/10000000000000:ℝ) ≤ wfun (x + y) := wc_744 (x + y) (by linarith) (by linarith)
                have hw5 : (177372543/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1445 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (1073/1024:ℝ) with hc | hc
          · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_98 x (by linarith) (by linarith)
            have hw1 : (239478321/1250000000000:ℝ) ≤ wfun y := wc_307 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
            have hw3 : (3526053/2500000000000:ℝ) ≤ wfun (x + y) := wc_736 (x + y) (by linarith) (by linarith)
            have hw5 : (706509509/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1406 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_98 x (by linarith) (by linarith)
            have hw1 : (239478321/1250000000000:ℝ) ≤ wfun y := wc_307 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
            have hw3 : (3526053/2500000000000:ℝ) ≤ wfun (x + y) := wc_736 (x + y) (by linarith) (by linarith)
            have hw5 : (168599037/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1438 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total x (1083/1024:ℝ) with hc | hc
        · rcases le_total z (1073/1024:ℝ) with hc | hc
          · rcases le_total y (24369/8192:ℝ) with hc | hc
            · have hw1 : (1635115293/10000000000000:ℝ) ≤ wfun y := wc_310 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
              have hw3 : (6078023/2000000000000:ℝ) ≤ wfun (x + y) := wc_751 (x + y) (by linarith) (by linarith)
              have hw5 : (782495959/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1424 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw1 : (686336349/5000000000000:ℝ) ≤ wfun y := wc_313 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
              have hw3 : (63585659/10000000000000:ℝ) ≤ wfun (x + y) := wc_767 (x + y) (by linarith) (by linarith)
              have hw4 : (1298021/5000000000000:ℝ) ≤ wfun (y + z) := wc_721 (y + z) (by linarith) (by linarith)
              have hw5 : (55778547/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1447 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (24369/8192:ℝ) with hc | hc
            · have hw1 : (1635115293/10000000000000:ℝ) ≤ wfun y := wc_310 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
              have hw3 : (6078023/2000000000000:ℝ) ≤ wfun (x + y) := wc_751 (x + y) (by linarith) (by linarith)
              have hw4 : (21693/40000000000:ℝ) ≤ wfun (y + z) := wc_725 (y + z) (by linarith) (by linarith)
              have hw5 : (925654441/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1448 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw1 : (686336349/5000000000000:ℝ) ≤ wfun y := wc_313 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
              have hw3 : (63585659/10000000000000:ℝ) ≤ wfun (x + y) := wc_767 (x + y) (by linarith) (by linarith)
              have hw4 : (11506103/5000000000000:ℝ) ≤ wfun (y + z) := wc_746 (y + z) (by linarith) (by linarith)
              have hw5 : (1044341323/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1465 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (1073/1024:ℝ) with hc | hc
          · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_98 x (by linarith) (by linarith)
            have hw1 : (136952521/1000000000000:ℝ) ≤ wfun y := wc_311 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
            have hw3 : (75190749/10000000000000:ℝ) ≤ wfun (x + y) := wc_768 (x + y) (by linarith) (by linarith)
            have hw5 : (461449393/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1449 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_98 x (by linarith) (by linarith)
            have hw1 : (136952521/1000000000000:ℝ) ≤ wfun y := wc_311 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
            have hw3 : (75190749/10000000000000:ℝ) ≤ wfun (x + y) := wc_768 (x + y) (by linarith) (by linarith)
            have hw4 : (1350713/2500000000000:ℝ) ≤ wfun (y + z) := wc_726 (y + z) (by linarith) (by linarith)
            have hw5 : (215367333/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1466 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total y (12169/4096:ℝ) with hc | hc
      · rcases le_total x (1083/1024:ℝ) with hc | hc
        · rcases le_total z (1083/1024:ℝ) with hc | hc
          · rcases le_total y (24307/8192:ℝ) with hc | hc
            · have hw1 : (2229636307/10000000000000:ℝ) ≤ wfun y := wc_306 y (by linarith) (by linarith)
              have hw3 : (32949/1000000000000:ℝ) ≤ wfun (x + y) := wc_711 (x + y) (by linarith) (by linarith)
              have hw4 : (32949/1000000000000:ℝ) ≤ wfun (y + z) := wc_711 (y + z) (by linarith) (by linarith)
              have hw5 : (169102719/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1437 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw1 : (240095521/1250000000000:ℝ) ≤ wfun y := wc_309 y (by linarith) (by linarith)
              have hw3 : (2319419/2500000000000:ℝ) ≤ wfun (x + y) := wc_731 (x + y) (by linarith) (by linarith)
              have hw4 : (2319419/2500000000000:ℝ) ≤ wfun (y + z) := wc_731 (y + z) (by linarith) (by linarith)
              have hw5 : (479710493/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1452 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw1 : (239478321/1250000000000:ℝ) ≤ wfun y := wc_307 y (by linarith) (by linarith)
            have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_98 z (by linarith) (by linarith)
            have hw3 : (1313/40000000000:ℝ) ≤ wfun (x + y) := wc_712 (x + y) (by linarith) (by linarith)
            have hw4 : (3526053/2500000000000:ℝ) ≤ wfun (y + z) := wc_736 (y + z) (by linarith) (by linarith)
            have hw5 : (990796899/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1458 (x + y + z) (by linarith) (by linarith)
            linarith
        · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_98 x (by linarith) (by linarith)
          have hw1 : (239478321/1250000000000:ℝ) ≤ wfun y := wc_307 y (by linarith) (by linarith)
          have hw3 : (3526053/2500000000000:ℝ) ≤ wfun (x + y) := wc_736 (x + y) (by linarith) (by linarith)
          have hw4 : (163329/5000000000000:ℝ) ≤ wfun (y + z) := wc_713 (y + z) (by linarith) (by linarith)
          have hw5 : (986997519/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1459 (x + y + z) (by linarith) (by linarith)
          linarith
      · have hw1 : (136952521/1000000000000:ℝ) ≤ wfun y := wc_311 y (by linarith) (by linarith)
        have hw3 : (7532357/2500000000000:ℝ) ≤ wfun (x + y) := wc_752 (x + y) (by linarith) (by linarith)
        have hw4 : (7532357/2500000000000:ℝ) ≤ wfun (y + z) := wc_752 (y + z) (by linarith) (by linarith)
        have hw5 : (534301079/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1467 (x + y + z) (by linarith) (by linarith)
        linarith

set_option maxHeartbeats 20000000 in
lemma ch_205 (x y z : ℝ) (hx1 : (63/64:ℝ) ≤ x) (hx2 : x ≤ (17/16:ℝ))
    (hy1 : (1525/512:ℝ) ≤ y) (hy2 : y ≤ (389/128:ℝ))
    (hz1 : (63/64:ℝ) ≤ z) (hz2 : z ≤ (17/16:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
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
                have hw1 : (137922559/2500000000000:ℝ) ≤ wfun y := wc_316 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_13 z (by linarith) (by linarith)
                have hw5 : (45928559/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1232 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total z (529/512:ℝ) with hc | hc
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
                  have hw1 : (137922559/2500000000000:ℝ) ≤ wfun y := wc_316 y (by linarith) (by linarith)
                  have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
                  have hw5 : (139560919/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1254 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total y (12231/4096:ℝ) with hc | hc
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
                    have hw1 : (183106839/2000000000000:ℝ) ≤ wfun y := wc_315 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_19 z (by linarith) (by linarith)
                    have hw5 : (283710363/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1294 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
                    have hw1 : (5534703/100000000000:ℝ) ≤ wfun y := wc_320 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_19 z (by linarith) (by linarith)
                    have hw3 : (1737357/2500000000000:ℝ) ≤ wfun (x + y) := wc_728 (x + y) (by linarith) (by linarith)
                    have hw4 : (1737357/2500000000000:ℝ) ≤ wfun (y + z) := wc_728 (y + z) (by linarith) (by linarith)
                    have hw5 : (214051577/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1331 (x + y + z) (by linarith) (by linarith)
                    linarith
            · rcases le_total x (529/512:ℝ) with hc | hc
              · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
                have hw1 : (102076243/10000000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (3:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_322 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_326 y (by linarith) (by linarith))
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_13 z (by linarith) (by linarith)
                have hw3 : (36159/250000000000:ℝ) ≤ wfun (x + y) := wc_717 (x + y) (by linarith) (by linarith)
                have hw4 : (1432423/10000000000000:ℝ) ≤ wfun (y + z) := wc_718 (y + z) (by linarith) (by linarith)
                have hw5 : (42053501/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1276 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total z (529/512:ℝ) with hc | hc
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
                  have hw1 : (102076243/10000000000000:ℝ) ≤ wfun y := by
                    rcases le_total y (3:ℝ) with hq10 | hq10
                    · exact le_trans (by norm_num) (wc_322 y (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_326 y (by linarith) (by linarith))
                  have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
                  have hw3 : (6897/1220703125:ℝ) ≤ wfun (x + y) := wc_766 (x + y) (by linarith) (by linarith)
                  have hw4 : (36159/250000000000:ℝ) ≤ wfun (y + z) := wc_717 (y + z) (by linarith) (by linarith)
                  have hw5 : (76188523/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1322 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
                  have hw1 : (102076243/10000000000000:ℝ) ≤ wfun y := by
                    rcases le_total y (3:ℝ) with hq10 | hq10
                    · exact le_trans (by norm_num) (wc_322 y (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_326 y (by linarith) (by linarith))
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_19 z (by linarith) (by linarith)
                  have hw3 : (6897/1220703125:ℝ) ≤ wfun (x + y) := wc_766 (x + y) (by linarith) (by linarith)
                  have hw4 : (6897/1220703125:ℝ) ≤ wfun (y + z) := wc_766 (y + z) (by linarith) (by linarith)
                  have hw5 : (298692789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1380 (x + y + z) (by linarith) (by linarith)
                  linarith
          · rcases le_total y (6131/2048:ℝ) with hc | hc
            · rcases le_total x (529/512:ℝ) with hc | hc
              · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
                have hw1 : (137922559/2500000000000:ℝ) ≤ wfun y := wc_316 y (by linarith) (by linarith)
                have hw4 : (8115287/5000000000000:ℝ) ≤ wfun (y + z) := wc_742 (y + z) (by linarith) (by linarith)
                have hw5 : (55971473/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1296 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total z (539/512:ℝ) with hc | hc
                · rcases le_total y (12231/4096:ℝ) with hc | hc
                  · rcases le_total x (1063/1024:ℝ) with hc | hc
                    · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
                      have hw1 : (183106839/2000000000000:ℝ) ≤ wfun y := wc_315 y (by linarith) (by linarith)
                      have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_41 z (by linarith) (by linarith)
                      have hw4 : (16511887/10000000000000:ℝ) ≤ wfun (y + z) := wc_740 (y + z) (by linarith) (by linarith)
                      have hw5 : (238608519/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1349 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · rcases le_total z (1073/1024:ℝ) with hc | hc
                      · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                        have hw1 : (183106839/2000000000000:ℝ) ≤ wfun y := wc_315 y (by linarith) (by linarith)
                        have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                        have hw3 : (198721/2500000000000:ℝ) ≤ wfun (x + y) := wc_716 (x + y) (by linarith) (by linarith)
                        have hw4 : (16592229/10000000000000:ℝ) ≤ wfun (y + z) := wc_739 (y + z) (by linarith) (by linarith)
                        have hw5 : (593510889/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1379 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                        have hw1 : (183106839/2000000000000:ℝ) ≤ wfun y := wc_315 y (by linarith) (by linarith)
                        have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
                        have hw3 : (198721/2500000000000:ℝ) ≤ wfun (x + y) := wc_716 (x + y) (by linarith) (by linarith)
                        have hw4 : (52510613/10000000000000:ℝ) ≤ wfun (y + z) := wc_765 (y + z) (by linarith) (by linarith)
                        have hw5 : (359821577/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1409 (x + y + z) (by linarith) (by linarith)
                        linarith
                  · rcases le_total x (1063/1024:ℝ) with hc | hc
                    · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
                      have hw1 : (5534703/100000000000:ℝ) ≤ wfun y := wc_320 y (by linarith) (by linarith)
                      have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_41 z (by linarith) (by linarith)
                      have hw3 : (349163/500000000000:ℝ) ≤ wfun (x + y) := wc_727 (x + y) (by linarith) (by linarith)
                      have hw4 : (5024187/625000000000:ℝ) ≤ wfun (y + z) := wc_770 (y + z) (by linarith) (by linarith)
                      have hw5 : (658907567/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1393 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                      have hw1 : (5534703/100000000000:ℝ) ≤ wfun y := wc_320 y (by linarith) (by linarith)
                      have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_41 z (by linarith) (by linarith)
                      have hw3 : (6773707/2000000000000:ℝ) ≤ wfun (x + y) := wc_753 (x + y) (by linarith) (by linarith)
                      have hw4 : (5024187/625000000000:ℝ) ≤ wfun (y + z) := wc_770 (y + z) (by linarith) (by linarith)
                      have hw5 : (395439643/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1425 (x + y + z) (by linarith) (by linarith)
                      linarith
                · rcases le_total y (12231/4096:ℝ) with hc | hc
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
                    have hw1 : (183106839/2000000000000:ℝ) ≤ wfun y := wc_315 y (by linarith) (by linarith)
                    have hw4 : (107845387/10000000000000:ℝ) ≤ wfun (y + z) := wc_775 (y + z) (by linarith) (by linarith)
                    have hw5 : (357063571/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1410 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
                    have hw1 : (5534703/100000000000:ℝ) ≤ wfun y := wc_320 y (by linarith) (by linarith)
                    have hw3 : (1737357/2500000000000:ℝ) ≤ wfun (x + y) := wc_728 (x + y) (by linarith) (by linarith)
                    have hw4 : (14547321/625000000000:ℝ) ≤ wfun (y + z) := wc_793 (y + z) (by linarith) (by linarith)
                    have hw5 : (930614427/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1451 (x + y + z) (by linarith) (by linarith)
                    linarith
            · rcases le_total x (529/512:ℝ) with hc | hc
              · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
                have hw1 : (102076243/10000000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (3:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_322 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_326 y (by linarith) (by linarith))
                have hw3 : (36159/250000000000:ℝ) ≤ wfun (x + y) := wc_717 (x + y) (by linarith) (by linarith)
                have hw4 : (188423087/10000000000000:ℝ) ≤ wfun (y + z) := wc_792 (y + z) (by linarith) (by linarith)
                have hw5 : (592818281/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1381 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
                have hw1 : (102076243/10000000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (3:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_322 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_326 y (by linarith) (by linarith))
                have hw3 : (6897/1220703125:ℝ) ≤ wfun (x + y) := wc_766 (x + y) (by linarith) (by linarith)
                have hw4 : (188423087/10000000000000:ℝ) ≤ wfun (y + z) := wc_792 (y + z) (by linarith) (by linarith)
                have hw5 : (853292617/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1444 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (267/256:ℝ) with hc | hc
          · rcases le_total y (6131/2048:ℝ) with hc | hc
            · rcases le_total x (539/512:ℝ) with hc | hc
              · rcases le_total z (529/512:ℝ) with hc | hc
                · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                  have hw1 : (137922559/2500000000000:ℝ) ≤ wfun y := wc_316 y (by linarith) (by linarith)
                  have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
                  have hw3 : (4097079/2500000000000:ℝ) ≤ wfun (x + y) := wc_741 (x + y) (by linarith) (by linarith)
                  have hw5 : (282019961/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1295 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total y (12231/4096:ℝ) with hc | hc
                  · rcases le_total x (1073/1024:ℝ) with hc | hc
                    · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
                      have hw1 : (183106839/2000000000000:ℝ) ≤ wfun y := wc_315 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_19 z (by linarith) (by linarith)
                      have hw3 : (16592229/10000000000000:ℝ) ≤ wfun (x + y) := wc_739 (x + y) (by linarith) (by linarith)
                      have hw5 : (238608519/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1349 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · rcases le_total z (1063/1024:ℝ) with hc | hc
                      · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
                        have hw1 : (183106839/2000000000000:ℝ) ≤ wfun y := wc_315 y (by linarith) (by linarith)
                        have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
                        have hw3 : (52510613/10000000000000:ℝ) ≤ wfun (x + y) := wc_765 (x + y) (by linarith) (by linarith)
                        have hw5 : (593510889/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1379 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
                        have hw1 : (183106839/2000000000000:ℝ) ≤ wfun y := wc_315 y (by linarith) (by linarith)
                        have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
                        have hw3 : (52510613/10000000000000:ℝ) ≤ wfun (x + y) := wc_765 (x + y) (by linarith) (by linarith)
                        have hw4 : (198721/2500000000000:ℝ) ≤ wfun (y + z) := wc_716 (y + z) (by linarith) (by linarith)
                        have hw5 : (359821577/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1409 (x + y + z) (by linarith) (by linarith)
                        linarith
                  · rcases le_total x (1073/1024:ℝ) with hc | hc
                    · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
                      have hw1 : (5534703/100000000000:ℝ) ≤ wfun y := wc_320 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_19 z (by linarith) (by linarith)
                      have hw3 : (80777393/10000000000000:ℝ) ≤ wfun (x + y) := wc_769 (x + y) (by linarith) (by linarith)
                      have hw4 : (1737357/2500000000000:ℝ) ≤ wfun (y + z) := wc_728 (y + z) (by linarith) (by linarith)
                      have hw5 : (658907567/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1393 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
                      have hw1 : (5534703/100000000000:ℝ) ≤ wfun y := wc_320 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_19 z (by linarith) (by linarith)
                      have hw3 : (36879733/2500000000000:ℝ) ≤ wfun (x + y) := wc_780 (x + y) (by linarith) (by linarith)
                      have hw4 : (1737357/2500000000000:ℝ) ≤ wfun (y + z) := wc_728 (y + z) (by linarith) (by linarith)
                      have hw5 : (395439643/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1425 (x + y + z) (by linarith) (by linarith)
                      linarith
              · rcases le_total z (529/512:ℝ) with hc | hc
                · have hw1 : (137922559/2500000000000:ℝ) ≤ wfun y := wc_316 y (by linarith) (by linarith)
                  have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
                  have hw3 : (428161/40000000000:ℝ) ≤ wfun (x + y) := wc_776 (x + y) (by linarith) (by linarith)
                  have hw5 : (236277491/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1350 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total y (12231/4096:ℝ) with hc | hc
                  · have hw1 : (183106839/2000000000000:ℝ) ≤ wfun y := wc_315 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_19 z (by linarith) (by linarith)
                    have hw3 : (107845387/10000000000000:ℝ) ≤ wfun (x + y) := wc_775 (x + y) (by linarith) (by linarith)
                    have hw5 : (357063571/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1410 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw1 : (5534703/100000000000:ℝ) ≤ wfun y := wc_320 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_19 z (by linarith) (by linarith)
                    have hw3 : (14547321/625000000000:ℝ) ≤ wfun (x + y) := wc_793 (x + y) (by linarith) (by linarith)
                    have hw4 : (1737357/2500000000000:ℝ) ≤ wfun (y + z) := wc_728 (y + z) (by linarith) (by linarith)
                    have hw5 : (930614427/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1451 (x + y + z) (by linarith) (by linarith)
                    linarith
            · rcases le_total x (539/512:ℝ) with hc | hc
              · rcases le_total z (529/512:ℝ) with hc | hc
                · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                  have hw1 : (102076243/10000000000000:ℝ) ≤ wfun y := by
                    rcases le_total y (3:ℝ) with hq10 | hq10
                    · exact le_trans (by norm_num) (wc_322 y (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_326 y (by linarith) (by linarith))
                  have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
                  have hw3 : (95123723/5000000000000:ℝ) ≤ wfun (x + y) := wc_791 (x + y) (by linarith) (by linarith)
                  have hw4 : (36159/250000000000:ℝ) ≤ wfun (y + z) := wc_717 (y + z) (by linarith) (by linarith)
                  have hw5 : (298692789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1380 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                  have hw1 : (102076243/10000000000000:ℝ) ≤ wfun y := by
                    rcases le_total y (3:ℝ) with hq10 | hq10
                    · exact le_trans (by norm_num) (wc_322 y (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_326 y (by linarith) (by linarith))
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_19 z (by linarith) (by linarith)
                  have hw3 : (95123723/5000000000000:ℝ) ≤ wfun (x + y) := wc_791 (x + y) (by linarith) (by linarith)
                  have hw4 : (6897/1220703125:ℝ) ≤ wfun (y + z) := wc_766 (y + z) (by linarith) (by linarith)
                  have hw5 : (429927023/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1443 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw1 : (102076243/10000000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (3:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_322 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_326 y (by linarith) (by linarith))
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_13 z (by linarith) (by linarith)
                have hw3 : (200521187/5000000000000:ℝ) ≤ wfun (x + y) := wc_808 (x + y) (by linarith) (by linarith)
                have hw4 : (1432423/10000000000000:ℝ) ≤ wfun (y + z) := wc_718 (y + z) (by linarith) (by linarith)
                have hw5 : (853292617/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1444 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (6131/2048:ℝ) with hc | hc
            · rcases le_total x (539/512:ℝ) with hc | hc
              · rcases le_total z (539/512:ℝ) with hc | hc
                · rcases le_total y (12231/4096:ℝ) with hc | hc
                  · rcases le_total x (1073/1024:ℝ) with hc | hc
                    · rcases le_total z (1073/1024:ℝ) with hc | hc
                      · rcases le_total y (24431/8192:ℝ) with hc | hc
                        · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
                          have hw1 : (566703343/5000000000000:ℝ) ≤ wfun y := wc_314 y (by linarith) (by linarith)
                          have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                          have hw3 : (16654831/10000000000000:ℝ) ≤ wfun (x + y) := wc_738 (x + y) (by linarith) (by linarith)
                          have hw4 : (16654831/10000000000000:ℝ) ≤ wfun (y + z) := wc_738 (y + z) (by linarith) (by linarith)
                          have hw5 : (28871797/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1408 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
                          have hw1 : (917274921/10000000000000:ℝ) ≤ wfun y := wc_318 y (by linarith) (by linarith)
                          have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                          have hw3 : (4284463/1000000000000:ℝ) ≤ wfun (x + y) := wc_755 (x + y) (by linarith) (by linarith)
                          have hw4 : (4284463/1000000000000:ℝ) ≤ wfun (y + z) := wc_755 (y + z) (by linarith) (by linarith)
                          have hw5 : (103472171/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1429 (x + y + z) (by linarith) (by linarith)
                          linarith
                      · rcases le_total y (24431/8192:ℝ) with hc | hc
                        · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
                          have hw1 : (566703343/5000000000000:ℝ) ≤ wfun y := wc_314 y (by linarith) (by linarith)
                          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
                          have hw3 : (16654831/10000000000000:ℝ) ≤ wfun (x + y) := wc_738 (x + y) (by linarith) (by linarith)
                          have hw4 : (5270849/1000000000000:ℝ) ≤ wfun (y + z) := wc_764 (y + z) (by linarith) (by linarith)
                          have hw5 : (859830283/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1442 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
                          have hw1 : (917274921/10000000000000:ℝ) ≤ wfun y := wc_318 y (by linarith) (by linarith)
                          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
                          have hw3 : (4284463/1000000000000:ℝ) ≤ wfun (x + y) := wc_755 (x + y) (by linarith) (by linarith)
                          have hw4 : (94426383/10000000000000:ℝ) ≤ wfun (y + z) := wc_771 (y + z) (by linarith) (by linarith)
                          have hw5 : (974610313/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1454 (x + y + z) (by linarith) (by linarith)
                          linarith
                    · rcases le_total z (1073/1024:ℝ) with hc | hc
                      · rcases le_total y (24431/8192:ℝ) with hc | hc
                        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
                          have hw1 : (566703343/5000000000000:ℝ) ≤ wfun y := wc_314 y (by linarith) (by linarith)
                          have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                          have hw3 : (5270849/1000000000000:ℝ) ≤ wfun (x + y) := wc_764 (x + y) (by linarith) (by linarith)
                          have hw4 : (16654831/10000000000000:ℝ) ≤ wfun (y + z) := wc_738 (y + z) (by linarith) (by linarith)
                          have hw5 : (859830283/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1442 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
                          have hw1 : (917274921/10000000000000:ℝ) ≤ wfun y := wc_318 y (by linarith) (by linarith)
                          have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                          have hw3 : (94426383/10000000000000:ℝ) ≤ wfun (x + y) := wc_771 (x + y) (by linarith) (by linarith)
                          have hw4 : (4284463/1000000000000:ℝ) ≤ wfun (y + z) := wc_755 (y + z) (by linarith) (by linarith)
                          have hw5 : (974610313/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1454 (x + y + z) (by linarith) (by linarith)
                          linarith
                      · rcases le_total y (24431/8192:ℝ) with hc | hc
                        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
                          have hw1 : (566703343/5000000000000:ℝ) ≤ wfun y := wc_314 y (by linarith) (by linarith)
                          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
                          have hw3 : (5270849/1000000000000:ℝ) ≤ wfun (x + y) := wc_764 (x + y) (by linarith) (by linarith)
                          have hw4 : (5270849/1000000000000:ℝ) ≤ wfun (y + z) := wc_764 (y + z) (by linarith) (by linarith)
                          have hw5 : (504597163/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1460 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
                          have hw1 : (917274921/10000000000000:ℝ) ≤ wfun y := wc_318 y (by linarith) (by linarith)
                          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
                          have hw3 : (94426383/10000000000000:ℝ) ≤ wfun (x + y) := wc_771 (x + y) (by linarith) (by linarith)
                          have hw4 : (94426383/10000000000000:ℝ) ≤ wfun (y + z) := wc_771 (y + z) (by linarith) (by linarith)
                          have hw5 : (1132610991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1469 (x + y + z) (by linarith) (by linarith)
                          linarith
                  · rcases le_total x (1073/1024:ℝ) with hc | hc
                    · rcases le_total z (1073/1024:ℝ) with hc | hc
                      · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
                        have hw1 : (5534703/100000000000:ℝ) ≤ wfun y := wc_320 y (by linarith) (by linarith)
                        have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                        have hw3 : (80777393/10000000000000:ℝ) ≤ wfun (x + y) := wc_769 (x + y) (by linarith) (by linarith)
                        have hw4 : (80777393/10000000000000:ℝ) ≤ wfun (y + z) := wc_769 (y + z) (by linarith) (by linarith)
                        have hw5 : (937791853/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1450 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
                        have hw1 : (5534703/100000000000:ℝ) ≤ wfun y := wc_320 y (by linarith) (by linarith)
                        have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
                        have hw3 : (80777393/10000000000000:ℝ) ≤ wfun (x + y) := wc_769 (x + y) (by linarith) (by linarith)
                        have hw4 : (36879733/2500000000000:ℝ) ≤ wfun (y + z) := wc_780 (y + z) (by linarith) (by linarith)
                        have hw5 : (546419271/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1468 (x + y + z) (by linarith) (by linarith)
                        linarith
                    · rcases le_total z (1073/1024:ℝ) with hc | hc
                      · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
                        have hw1 : (5534703/100000000000:ℝ) ≤ wfun y := wc_320 y (by linarith) (by linarith)
                        have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                        have hw3 : (36879733/2500000000000:ℝ) ≤ wfun (x + y) := wc_780 (x + y) (by linarith) (by linarith)
                        have hw4 : (80777393/10000000000000:ℝ) ≤ wfun (y + z) := wc_769 (y + z) (by linarith) (by linarith)
                        have hw5 : (546419271/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1468 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
                        have hw1 : (5534703/100000000000:ℝ) ≤ wfun y := wc_320 y (by linarith) (by linarith)
                        have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
                        have hw3 : (36879733/2500000000000:ℝ) ≤ wfun (x + y) := wc_780 (x + y) (by linarith) (by linarith)
                        have hw4 : (36879733/2500000000000:ℝ) ≤ wfun (y + z) := wc_780 (y + z) (by linarith) (by linarith)
                        have hw5 : (251770887/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1483 (x + y + z) (by linarith) (by linarith)
                        linarith
                · rcases le_total y (12231/4096:ℝ) with hc | hc
                  · rcases le_total x (1073/1024:ℝ) with hc | hc
                    · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
                      have hw1 : (183106839/2000000000000:ℝ) ≤ wfun y := wc_315 y (by linarith) (by linarith)
                      have hw3 : (16592229/10000000000000:ℝ) ≤ wfun (x + y) := wc_739 (x + y) (by linarith) (by linarith)
                      have hw4 : (107845387/10000000000000:ℝ) ≤ wfun (y + z) := wc_775 (y + z) (by linarith) (by linarith)
                      have hw5 : (1002333521/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1462 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
                      have hw1 : (183106839/2000000000000:ℝ) ≤ wfun y := wc_315 y (by linarith) (by linarith)
                      have hw3 : (52510613/10000000000000:ℝ) ≤ wfun (x + y) := wc_765 (x + y) (by linarith) (by linarith)
                      have hw4 : (107845387/10000000000000:ℝ) ≤ wfun (y + z) := wc_775 (y + z) (by linarith) (by linarith)
                      have hw5 : (1161734083/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1480 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                    have hw1 : (5534703/100000000000:ℝ) ≤ wfun y := wc_320 y (by linarith) (by linarith)
                    have hw3 : (5024187/625000000000:ℝ) ≤ wfun (x + y) := wc_770 (x + y) (by linarith) (by linarith)
                    have hw4 : (14547321/625000000000:ℝ) ≤ wfun (y + z) := wc_793 (y + z) (by linarith) (by linarith)
                    have hw5 : (1249238179/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1484 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total z (539/512:ℝ) with hc | hc
                · rcases le_total y (12231/4096:ℝ) with hc | hc
                  · rcases le_total x (1083/1024:ℝ) with hc | hc
                    · rcases le_total z (1073/1024:ℝ) with hc | hc
                      · have hw1 : (183106839/2000000000000:ℝ) ≤ wfun y := wc_315 y (by linarith) (by linarith)
                        have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                        have hw3 : (108368853/10000000000000:ℝ) ≤ wfun (x + y) := wc_774 (x + y) (by linarith) (by linarith)
                        have hw4 : (16592229/10000000000000:ℝ) ≤ wfun (y + z) := wc_739 (y + z) (by linarith) (by linarith)
                        have hw5 : (251547891/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1461 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw1 : (183106839/2000000000000:ℝ) ≤ wfun y := wc_315 y (by linarith) (by linarith)
                        have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
                        have hw3 : (108368853/10000000000000:ℝ) ≤ wfun (x + y) := wc_774 (x + y) (by linarith) (by linarith)
                        have hw4 : (52510613/10000000000000:ℝ) ≤ wfun (y + z) := wc_765 (y + z) (by linarith) (by linarith)
                        have hw5 : (583100681/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1479 (x + y + z) (by linarith) (by linarith)
                        linarith
                    · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_98 x (by linarith) (by linarith)
                      have hw1 : (183106839/2000000000000:ℝ) ≤ wfun y := wc_315 y (by linarith) (by linarith)
                      have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_41 z (by linarith) (by linarith)
                      have hw3 : (22996019/1250000000000:ℝ) ≤ wfun (x + y) := wc_790 (x + y) (by linarith) (by linarith)
                      have hw4 : (16511887/10000000000000:ℝ) ≤ wfun (y + z) := wc_740 (y + z) (by linarith) (by linarith)
                      have hw5 : (1161734083/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1480 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw1 : (5534703/100000000000:ℝ) ≤ wfun y := wc_320 y (by linarith) (by linarith)
                    have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_41 z (by linarith) (by linarith)
                    have hw3 : (14547321/625000000000:ℝ) ≤ wfun (x + y) := wc_793 (x + y) (by linarith) (by linarith)
                    have hw4 : (5024187/625000000000:ℝ) ≤ wfun (y + z) := wc_770 (y + z) (by linarith) (by linarith)
                    have hw5 : (1249238179/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1484 (x + y + z) (by linarith) (by linarith)
                    linarith
                · have hw1 : (137922559/2500000000000:ℝ) ≤ wfun y := wc_316 y (by linarith) (by linarith)
                  have hw3 : (428161/40000000000:ℝ) ≤ wfun (x + y) := wc_776 (x + y) (by linarith) (by linarith)
                  have hw4 : (428161/40000000000:ℝ) ≤ wfun (y + z) := wc_776 (y + z) (by linarith) (by linarith)
                  have hw5 : (1319026531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1487 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total x (539/512:ℝ) with hc | hc
              · rcases le_total z (539/512:ℝ) with hc | hc
                · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                  have hw1 : (102076243/10000000000000:ℝ) ≤ wfun y := by
                    rcases le_total y (3:ℝ) with hq10 | hq10
                    · exact le_trans (by norm_num) (wc_322 y (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_326 y (by linarith) (by linarith))
                  have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_41 z (by linarith) (by linarith)
                  have hw3 : (95123723/5000000000000:ℝ) ≤ wfun (x + y) := wc_791 (x + y) (by linarith) (by linarith)
                  have hw4 : (95123723/5000000000000:ℝ) ≤ wfun (y + z) := wc_791 (y + z) (by linarith) (by linarith)
                  have hw5 : (583409317/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1481 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                  have hw1 : (102076243/10000000000000:ℝ) ≤ wfun y := by
                    rcases le_total y (3:ℝ) with hq10 | hq10
                    · exact le_trans (by norm_num) (wc_322 y (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_326 y (by linarith) (by linarith))
                  have hw3 : (95123723/5000000000000:ℝ) ≤ wfun (x + y) := wc_791 (x + y) (by linarith) (by linarith)
                  have hw4 : (200521187/5000000000000:ℝ) ≤ wfun (y + z) := wc_808 (y + z) (by linarith) (by linarith)
                  have hw5 : (189574513/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1492 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw1 : (102076243/10000000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (3:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_322 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_326 y (by linarith) (by linarith))
                have hw3 : (200521187/5000000000000:ℝ) ≤ wfun (x + y) := wc_808 (x + y) (by linarith) (by linarith)
                have hw4 : (188423087/10000000000000:ℝ) ≤ wfun (y + z) := wc_792 (y + z) (by linarith) (by linarith)
                have hw5 : (1505067239/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1493 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total x (267/256:ℝ) with hc | hc
        · rcases le_total z (267/256:ℝ) with hc | hc
          · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
            have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_13 z (by linarith) (by linarith)
            have hw3 : (58750599/5000000000000:ℝ) ≤ wfun (x + y) := wc_777 (x + y) (by linarith) (by linarith)
            have hw4 : (58750599/5000000000000:ℝ) ≤ wfun (y + z) := wc_777 (y + z) (by linarith) (by linarith)
            have hw5 : (480942433/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1353 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
            have hw3 : (58750599/5000000000000:ℝ) ≤ wfun (x + y) := wc_777 (x + y) (by linarith) (by linarith)
            have hw4 : (267941559/5000000000000:ℝ) ≤ wfun (y + z) := wc_815 (y + z) (by linarith) (by linarith)
            have hw5 : (199185017/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1463 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (267/256:ℝ) with hc | hc
          · have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_13 z (by linarith) (by linarith)
            have hw3 : (267941559/5000000000000:ℝ) ≤ wfun (x + y) := wc_815 (x + y) (by linarith) (by linarith)
            have hw4 : (58750599/5000000000000:ℝ) ≤ wfun (y + z) := wc_777 (y + z) (by linarith) (by linarith)
            have hw5 : (199185017/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1463 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw3 : (267941559/5000000000000:ℝ) ≤ wfun (x + y) := wc_815 (x + y) (by linarith) (by linarith)
            have hw4 : (267941559/5000000000000:ℝ) ≤ wfun (y + z) := wc_815 (y + z) (by linarith) (by linarith)
            have hw5 : (1680579671/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1496 (x + y + z) (by linarith) (by linarith)
            linarith

set_option maxHeartbeats 20000000 in
lemma ch_206 (x y z : ℝ) (hx1 : (63/64:ℝ) ≤ x) (hx2 : x ≤ (17/16:ℝ))
    (hy1 : (747/256:ℝ) ≤ y) (hy2 : y ≤ (389/128:ℝ))
    (hz1 : (17/16:ℝ) ≤ z) (hz2 : z ≤ (73/64:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
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
      have hw1 : (261299809/2000000000000:ℝ) ≤ wfun y := wc_292 y (by linarith) (by linarith)
      have hw2 : (15429929/1000000000000:ℝ) ≤ wfun z := wc_104 z (by linarith) (by linarith)
      have hw3 : (76620491/10000000000000:ℝ) ≤ wfun (x + y) := by
        rcases le_total (x + y) (4:ℝ) with hq30 | hq30
        · exact le_trans (by norm_num) (wc_626 (x + y) (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_663 (x + y) (by linarith) (by linarith))
      linarith
    · rcases le_total z (141/128:ℝ) with hc | hc
      · rcases le_total y (3019/1024:ℝ) with hc | hc
        · rcases le_total x (267/256:ℝ) with hc | hc
          · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
            have hw1 : (100676353/250000000000:ℝ) ≤ wfun y := wc_291 y (by linarith) (by linarith)
            have hw2 : (44604923/2500000000000:ℝ) ≤ wfun z := wc_103 z (by linarith) (by linarith)
            have hw3 : (122092393/5000000000000:ℝ) ≤ wfun (x + y) := wc_629 (x + y) (by linarith) (by linarith)
            linarith
          · rcases le_total z (277/256:ℝ) with hc | hc
            · rcases le_total y (6007/2048:ℝ) with hc | hc
              · have hw1 : (2995265257/5000000000000:ℝ) ≤ wfun y := wc_290 y (by linarith) (by linarith)
                have hw2 : (38452957/2000000000000:ℝ) ≤ wfun z := wc_102 z (by linarith) (by linarith)
                have hw3 : (82600037/5000000000000:ℝ) ≤ wfun (x + y) := wc_633 (x + y) (by linarith) (by linarith)
                have hw4 : (4221/10000000000000:ℝ) ≤ wfun (y + z) := by
                  rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                  · exact le_trans (by norm_num) (wc_644 (y + z) (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_677 (y + z) (by linarith) (by linarith))
                have hw5 : (33101423/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1226 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw1 : (816631931/2000000000000:ℝ) ≤ wfun y := wc_294 y (by linarith) (by linarith)
                have hw2 : (38452957/2000000000000:ℝ) ≤ wfun z := wc_102 z (by linarith) (by linarith)
                have hw3 : (436723/500000000000:ℝ) ≤ wfun (x + y) := by
                  rcases le_total (x + y) (4:ℝ) with hq30 | hq30
                  · exact le_trans (by norm_num) (wc_640 (x + y) (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_673 (x + y) (by linarith) (by linarith))
                have hw5 : (181069953/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1260 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw1 : (100676353/250000000000:ℝ) ≤ wfun y := wc_291 y (by linarith) (by linarith)
              have hw2 : (4137262453/10000000000000:ℝ) ≤ wfun z := wc_107 z (by linarith) (by linarith)
              have hw3 : (436723/500000000000:ℝ) ≤ wfun (x + y) := by
                rcases le_total (x + y) (4:ℝ) with hq30 | hq30
                · exact le_trans (by norm_num) (wc_634 (x + y) (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_673 (x + y) (by linarith) (by linarith))
              have hw5 : (242928173/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1281 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (267/256:ℝ) with hc | hc
          · rcases le_total z (277/256:ℝ) with hc | hc
            · rcases le_total y (6069/2048:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
                have hw1 : (2539642107/10000000000000:ℝ) ≤ wfun y := wc_298 y (by linarith) (by linarith)
                have hw2 : (38452957/2000000000000:ℝ) ≤ wfun z := wc_102 z (by linarith) (by linarith)
                have hw3 : (34242453/10000000000000:ℝ) ≤ wfun (x + y) := by
                  rcases le_total (x + y) (4:ℝ) with hq30 | hq30
                  · exact le_trans (by norm_num) (wc_638 (x + y) (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_669 (x + y) (by linarith) (by linarith))
                have hw5 : (31511369/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1252 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total x (529/512:ℝ) with hc | hc
                · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
                  have hw1 : (1362675081/10000000000000:ℝ) ≤ wfun y := wc_308 y (by linarith) (by linarith)
                  have hw2 : (38452957/2000000000000:ℝ) ≤ wfun z := wc_102 z (by linarith) (by linarith)
                  have hw3 : (2673983/5000000000000:ℝ) ≤ wfun (x + y) := by
                    rcases le_total (x + y) (4:ℝ) with hq30 | hq30
                    · exact le_trans (by norm_num) (wc_651 (x + y) (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_675 (x + y) (by linarith) (by linarith))
                  have hw4 : (11743211/2500000000000:ℝ) ≤ wfun (y + z) := wc_763 (y + z) (by linarith) (by linarith)
                  have hw5 : (14364449/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1321 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
                  have hw1 : (1362675081/10000000000000:ℝ) ≤ wfun y := wc_308 y (by linarith) (by linarith)
                  have hw2 : (38452957/2000000000000:ℝ) ≤ wfun z := wc_102 z (by linarith) (by linarith)
                  have hw4 : (11743211/2500000000000:ℝ) ≤ wfun (y + z) := wc_763 (y + z) (by linarith) (by linarith)
                  have hw5 : (569259631/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1378 (x + y + z) (by linarith) (by linarith)
                  linarith
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
              have hw1 : (67339097/500000000000:ℝ) ≤ wfun y := wc_299 y (by linarith) (by linarith)
              have hw2 : (4137262453/10000000000000:ℝ) ≤ wfun z := wc_107 z (by linarith) (by linarith)
              have hw4 : (92147329/10000000000000:ℝ) ≤ wfun (y + z) := wc_773 (y + z) (by linarith) (by linarith)
              have hw5 : (439255509/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1343 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (277/256:ℝ) with hc | hc
            · rcases le_total y (6069/2048:ℝ) with hc | hc
              · rcases le_total x (539/512:ℝ) with hc | hc
                · rcases le_total z (549/512:ℝ) with hc | hc
                  · rcases le_total y (12107/4096:ℝ) with hc | hc
                    · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                      have hw1 : (3285883949/10000000000000:ℝ) ≤ wfun y := wc_297 y (by linarith) (by linarith)
                      have hw2 : (9984781/500000000000:ℝ) ≤ wfun z := wc_101 z (by linarith) (by linarith)
                      have hw3 : (9692591/5000000000000:ℝ) ≤ wfun (x + y) := by
                        rcases le_total (x + y) (4:ℝ) with hq30 | hq30
                        · exact le_trans (by norm_num) (wc_653 (x + y) (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_671 (x + y) (by linarith) (by linarith))
                      have hw5 : (227036969/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1342 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                      have hw1 : (319327517/1250000000000:ℝ) ≤ wfun y := wc_304 y (by linarith) (by linarith)
                      have hw2 : (9984781/500000000000:ℝ) ≤ wfun z := wc_101 z (by linarith) (by linarith)
                      have hw4 : (2002543/5000000000000:ℝ) ≤ wfun (y + z) := wc_722 (y + z) (by linarith) (by linarith)
                      have hw5 : (63145721/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_1390 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                    have hw1 : (2539642107/10000000000000:ℝ) ≤ wfun y := wc_298 y (by linarith) (by linarith)
                    have hw2 : (1609622259/10000000000000:ℝ) ≤ wfun z := wc_106 z (by linarith) (by linarith)
                    have hw4 : (11672323/10000000000000:ℝ) ≤ wfun (y + z) := wc_735 (y + z) (by linarith) (by linarith)
                    have hw5 : (342044549/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1402 (x + y + z) (by linarith) (by linarith)
                    linarith
                · have hw1 : (2539642107/10000000000000:ℝ) ≤ wfun y := wc_298 y (by linarith) (by linarith)
                  have hw2 : (38452957/2000000000000:ℝ) ≤ wfun z := wc_102 z (by linarith) (by linarith)
                  have hw5 : (339431207/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1403 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total x (539/512:ℝ) with hc | hc
                · rcases le_total z (549/512:ℝ) with hc | hc
                  · rcases le_total y (12169/4096:ℝ) with hc | hc
                    · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                      have hw1 : (239478321/1250000000000:ℝ) ≤ wfun y := wc_307 y (by linarith) (by linarith)
                      have hw2 : (9984781/500000000000:ℝ) ≤ wfun z := wc_101 z (by linarith) (by linarith)
                      have hw4 : (9557219/2000000000000:ℝ) ≤ wfun (y + z) := wc_761 (y + z) (by linarith) (by linarith)
                      have hw5 : (418269633/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1439 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                      have hw1 : (136952521/1000000000000:ℝ) ≤ wfun y := wc_311 y (by linarith) (by linarith)
                      have hw2 : (9984781/500000000000:ℝ) ≤ wfun z := wc_101 z (by linarith) (by linarith)
                      have hw4 : (17410303/1250000000000:ℝ) ≤ wfun (y + z) := wc_779 (y + z) (by linarith) (by linarith)
                      have hw5 : (534301079/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1467 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                    have hw1 : (1362675081/10000000000000:ℝ) ≤ wfun y := wc_308 y (by linarith) (by linarith)
                    have hw2 : (1609622259/10000000000000:ℝ) ≤ wfun z := wc_106 z (by linarith) (by linarith)
                    have hw4 : (86688141/5000000000000:ℝ) ≤ wfun (y + z) := wc_789 (y + z) (by linarith) (by linarith)
                    have hw5 : (1134166649/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1477 (x + y + z) (by linarith) (by linarith)
                    linarith
                · have hw1 : (1362675081/10000000000000:ℝ) ≤ wfun y := wc_308 y (by linarith) (by linarith)
                  have hw2 : (38452957/2000000000000:ℝ) ≤ wfun z := wc_102 z (by linarith) (by linarith)
                  have hw3 : (32421/1000000000000:ℝ) ≤ wfun (x + y) := wc_714 (x + y) (by linarith) (by linarith)
                  have hw4 : (11743211/2500000000000:ℝ) ≤ wfun (y + z) := wc_763 (y + z) (by linarith) (by linarith)
                  have hw5 : (1125526841/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1478 (x + y + z) (by linarith) (by linarith)
                  linarith
            · have hw1 : (67339097/500000000000:ℝ) ≤ wfun y := wc_299 y (by linarith) (by linarith)
              have hw2 : (4137262453/10000000000000:ℝ) ≤ wfun z := wc_107 z (by linarith) (by linarith)
              have hw4 : (92147329/10000000000000:ℝ) ≤ wfun (y + z) := wc_773 (y + z) (by linarith) (by linarith)
              have hw5 : (936576257/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1457 (x + y + z) (by linarith) (by linarith)
              linarith
      · have hw1 : (261299809/2000000000000:ℝ) ≤ wfun y := wc_292 y (by linarith) (by linarith)
        have hw2 : (11778340313/10000000000000:ℝ) ≤ wfun z := wc_108 z (by linarith) (by linarith)
        have hw4 : (1440757/2000000000000:ℝ) ≤ wfun (y + z) := wc_729 (y + z) (by linarith) (by linarith)
        have hw5 : (46032101/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1283 (x + y + z) (by linarith) (by linarith)
        linarith
  · rcases le_total x (131/128:ℝ) with hc | hc
    · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := by
        rcases le_total x (1:ℝ) with hq00 | hq00
        · exact le_trans (by norm_num) (wc_5 x (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_7 x (by linarith) (by linarith))
      have hw2 : (15429929/1000000000000:ℝ) ≤ wfun z := wc_104 z (by linarith) (by linarith)
      have hw4 : (246785359/10000000000000:ℝ) ≤ wfun (y + z) := wc_800 (y + z) (by linarith) (by linarith)
      have hw5 : (41391449/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1234 (x + y + z) (by linarith) (by linarith)
      linarith
    · rcases le_total z (141/128:ℝ) with hc | hc
      · rcases le_total y (3081/1024:ℝ) with hc | hc
        · rcases le_total x (267/256:ℝ) with hc | hc
          · rcases le_total z (277/256:ℝ) with hc | hc
            · rcases le_total y (6131/2048:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
                have hw1 : (137922559/2500000000000:ℝ) ≤ wfun y := wc_316 y (by linarith) (by linarith)
                have hw2 : (38452957/2000000000000:ℝ) ≤ wfun z := wc_102 z (by linarith) (by linarith)
                have hw4 : (273038177/10000000000000:ℝ) ≤ wfun (y + z) := wc_796 (y + z) (by linarith) (by linarith)
                have hw5 : (699094733/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1411 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
                have hw1 : (102076243/10000000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (3:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_322 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_326 y (by linarith) (by linarith))
                have hw2 : (38452957/2000000000000:ℝ) ≤ wfun z := wc_102 z (by linarith) (by linarith)
                have hw3 : (1432423/10000000000000:ℝ) ≤ wfun (x + y) := wc_718 (x + y) (by linarith) (by linarith)
                have hw4 : (170103471/2500000000000:ℝ) ≤ wfun (y + z) := wc_836 (y + z) (by linarith) (by linarith)
                have hw5 : (1149129417/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1482 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
              have hw1 : (102076243/10000000000000:ℝ) ≤ wfun y := by
                rcases le_total y (3:ℝ) with hq10 | hq10
                · exact le_trans (by norm_num) (wc_317 y (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_326 y (by linarith) (by linarith))
              have hw2 : (4137262453/10000000000000:ℝ) ≤ wfun z := wc_107 z (by linarith) (by linarith)
              have hw4 : (32774279/400000000000:ℝ) ≤ wfun (y + z) := wc_853 (y + z) (by linarith) (by linarith)
              have hw5 : (641911203/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1488 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw1 : (102076243/10000000000000:ℝ) ≤ wfun y := by
              rcases le_total y (3:ℝ) with hq10 | hq10
              · exact le_trans (by norm_num) (wc_317 y (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_326 y (by linarith) (by linarith))
            have hw2 : (44604923/2500000000000:ℝ) ≤ wfun z := wc_103 z (by linarith) (by linarith)
            have hw3 : (999363/625000000000:ℝ) ≤ wfun (x + y) := wc_743 (x + y) (by linarith) (by linarith)
            have hw4 : (263915387/10000000000000:ℝ) ≤ wfun (y + z) := wc_798 (y + z) (by linarith) (by linarith)
            have hw5 : (252901217/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1489 (x + y + z) (by linarith) (by linarith)
            linarith
        · have hw2 : (44604923/2500000000000:ℝ) ≤ wfun z := wc_103 z (by linarith) (by linarith)
          have hw3 : (7204521/625000000000:ℝ) ≤ wfun (x + y) := wc_778 (x + y) (by linarith) (by linarith)
          have hw4 : (1219525351/10000000000000:ℝ) ≤ wfun (y + z) := wc_956 (y + z) (by linarith) (by linarith)
          have hw5 : (815292227/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1497 (x + y + z) (by linarith) (by linarith)
          linarith
      · have hw2 : (11778340313/10000000000000:ℝ) ≤ wfun z := wc_108 z (by linarith) (by linarith)
        have hw4 : (1572805651/10000000000000:ℝ) ≤ wfun (y + z) := wc_1117 (y + z) (by linarith) (by linarith)
        have hw5 : (1934302493/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1498 (x + y + z) (by linarith) (by linarith)
        linarith

end Zeta23Ext.Bridge.FourPoint
