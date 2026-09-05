import FourPoint.Cells

/-! Chunk module 2 of 16 of the three-dimensional table.  Each lemma is one
subtree of at most 110 leaves of one box's bisection tree; `FourPoint/Boxes.lean` routes
the box down to them.  Cutting the tree this way gives each subtree its own
heartbeat budget and lets `lake` compile them in parallel. -/

noncomputable section
namespace Zeta23Ext.Bridge.FourPoint

set_option maxHeartbeats 20000000 in
lemma ch_21 (x y z : ℝ) (hx1 : (1063/1024:ℝ) ≤ x) (hx2 : x ≤ (2131/2048:ℝ))
    (hy1 : (1013/512:ℝ) ≤ y) (hy2 : y ≤ (2031/1024:ℝ))
    (hz1 : (267/256:ℝ) ≤ z) (hz2 : z ≤ (1073/1024:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total y (4057/2048:ℝ) with hc | hc
  · rcases le_total z (2141/2048:ℝ) with hc | hc
    · rcases le_total x (4257/4096:ℝ) with hc | hc
      · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
        have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_163 y (by linarith) (by linarith)
        have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
        have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_361 (y + z) (by linarith) (by linarith)
        have hw5 : (81942717/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_846 (x + y + z) (by linarith) (by linarith)
        linarith
      · rcases le_total y (8109/4096:ℝ) with hc | hc
        · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
          have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_162 y (by linarith) (by linarith)
          have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
          have hw4 : (29587/250000000000:ℝ) ≤ wfun (y + z) := wc_360 (y + z) (by linarith) (by linarith)
          have hw5 : (865374359/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_855 (x + y + z) (by linarith) (by linarith)
          linarith
        · rcases le_total z (4277/4096:ℝ) with hc | hc
          · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
            have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_172 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
            have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_374 (y + z) (by linarith) (by linarith)
            have hw5 : (3564753/39062500000:ℝ) ≤ wfun (x + y + z) := wc_857 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
            have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_172 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
            have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_387 (y + z) (by linarith) (by linarith)
            have hw5 : (959876941/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_865 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total x (4257/4096:ℝ) with hc | hc
      · rcases le_total y (8109/4096:ℝ) with hc | hc
        · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
          have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_162 y (by linarith) (by linarith)
          have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
          have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_348 (x + y) (by linarith) (by linarith)
          have hw4 : (649907/625000000000:ℝ) ≤ wfun (y + z) := wc_388 (y + z) (by linarith) (by linarith)
          have hw5 : (227869559/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_858 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
          have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_172 y (by linarith) (by linarith)
          have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
          have hw4 : (736743/400000000000:ℝ) ≤ wfun (y + z) := wc_404 (y + z) (by linarith) (by linarith)
          have hw5 : (958721819/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_866 (x + y + z) (by linarith) (by linarith)
          linarith
      · rcases le_total y (8109/4096:ℝ) with hc | hc
        · rcases le_total z (4287/4096:ℝ) with hc | hc
          · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
            have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_162 y (by linarith) (by linarith)
            have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
            have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_387 (y + z) (by linarith) (by linarith)
            have hw5 : (959876941/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_865 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
            have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_162 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
            have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_403 (y + z) (by linarith) (by linarith)
            have hw5 : (126039153/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_871 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (4287/4096:ℝ) with hc | hc
          · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
            have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_172 y (by linarith) (by linarith)
            have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
            have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_403 (y + z) (by linarith) (by linarith)
            have hw5 : (126039153/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_871 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
            have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_172 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
            have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_417 (y + z) (by linarith) (by linarith)
            have hw5 : (1057880619/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_887 (x + y + z) (by linarith) (by linarith)
            linarith
  · rcases le_total z (2141/2048:ℝ) with hc | hc
    · rcases le_total x (4257/4096:ℝ) with hc | hc
      · rcases le_total y (8119/4096:ℝ) with hc | hc
        · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
          have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_179 y (by linarith) (by linarith)
          have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
          have hw4 : (649907/625000000000:ℝ) ≤ wfun (y + z) := wc_388 (y + z) (by linarith) (by linarith)
          have hw5 : (227869559/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_858 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
          have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
          have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
          have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_353 (x + y) (by linarith) (by linarith)
          have hw4 : (736743/400000000000:ℝ) ≤ wfun (y + z) := wc_404 (y + z) (by linarith) (by linarith)
          have hw5 : (958721819/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_866 (x + y + z) (by linarith) (by linarith)
          linarith
      · rcases le_total y (8119/4096:ℝ) with hc | hc
        · rcases le_total z (4277/4096:ℝ) with hc | hc
          · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
            have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_179 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
            have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_353 (x + y) (by linarith) (by linarith)
            have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_387 (y + z) (by linarith) (by linarith)
            have hw5 : (959876941/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_865 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
            have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_179 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
            have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_353 (x + y) (by linarith) (by linarith)
            have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_403 (y + z) (by linarith) (by linarith)
            have hw5 : (126039153/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_871 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (4277/4096:ℝ) with hc | hc
          · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
            have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
            have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_359 (x + y) (by linarith) (by linarith)
            have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_403 (y + z) (by linarith) (by linarith)
            have hw5 : (126039153/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_871 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
            have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
            have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_359 (x + y) (by linarith) (by linarith)
            have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_417 (y + z) (by linarith) (by linarith)
            have hw5 : (1057880619/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_887 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total x (4257/4096:ℝ) with hc | hc
      · rcases le_total y (8119/4096:ℝ) with hc | hc
        · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
          have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_179 y (by linarith) (by linarith)
          have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
          have hw4 : (2870559/1000000000000:ℝ) ≤ wfun (y + z) := wc_418 (y + z) (by linarith) (by linarith)
          have hw5 : (1007100179/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_872 (x + y + z) (by linarith) (by linarith)
          linarith
        · rcases le_total z (4287/4096:ℝ) with hc | hc
          · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
            have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
            have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
            have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_353 (x + y) (by linarith) (by linarith)
            have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_435 (y + z) (by linarith) (by linarith)
            have hw5 : (1057880619/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_887 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
            have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
            have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_353 (x + y) (by linarith) (by linarith)
            have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_449 (y + z) (by linarith) (by linarith)
            have hw5 : (1108574073/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_896 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total y (8119/4096:ℝ) with hc | hc
        · rcases le_total z (4287/4096:ℝ) with hc | hc
          · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
            have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_179 y (by linarith) (by linarith)
            have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
            have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_353 (x + y) (by linarith) (by linarith)
            have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_417 (y + z) (by linarith) (by linarith)
            have hw5 : (1057880619/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_887 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
            have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_179 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
            have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_353 (x + y) (by linarith) (by linarith)
            have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_435 (y + z) (by linarith) (by linarith)
            have hw5 : (1108574073/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_896 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (4287/4096:ℝ) with hc | hc
          · rcases le_total x (8519/8192:ℝ) with hc | hc
            · have hw0 : (482068367/2000000000000:ℝ) ≤ wfun x := wc_26 x (by linarith) (by linarith)
              have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (593183/5000000000000:ℝ) ≤ wfun (x + y) := wc_358 (x + y) (by linarith) (by linarith)
              have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_435 (y + z) (by linarith) (by linarith)
              have hw5 : (554620627/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_895 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_28 x (by linarith) (by linarith)
              have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (2638657/10000000000000:ℝ) ≤ wfun (x + y) := wc_369 (x + y) (by linarith) (by linarith)
              have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_435 (y + z) (by linarith) (by linarith)
              have hw5 : (1135024061/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_904 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (8519/8192:ℝ) with hc | hc
            · have hw0 : (482068367/2000000000000:ℝ) ≤ wfun x := wc_26 x (by linarith) (by linarith)
              have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (593183/5000000000000:ℝ) ≤ wfun (x + y) := wc_358 (x + y) (by linarith) (by linarith)
              have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_449 (y + z) (by linarith) (by linarith)
              have hw5 : (36283957/312500000000:ℝ) ≤ wfun (x + y + z) := wc_908 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_28 x (by linarith) (by linarith)
              have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (2638657/10000000000000:ℝ) ≤ wfun (x + y) := wc_369 (x + y) (by linarith) (by linarith)
              have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_449 (y + z) (by linarith) (by linarith)
              have hw5 : (118742829/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_916 (x + y + z) (by linarith) (by linarith)
              linarith

set_option maxHeartbeats 20000000 in
lemma ch_28 (x y z : ℝ) (hx1 : (1063/1024:ℝ) ≤ x) (hx2 : x ≤ (267/256:ℝ))
    (hy1 : (2031/1024:ℝ) ≤ y) (hy2 : y ≤ (509/256:ℝ))
    (hz1 : (1073/1024:ℝ) ≤ z) (hz2 : z ≤ (539/512:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (2131/2048:ℝ) with hc | hc
  · rcases le_total y (4067/2048:ℝ) with hc | hc
    · rcases le_total z (2151/2048:ℝ) with hc | hc
      · rcases le_total x (4257/4096:ℝ) with hc | hc
        · rcases le_total y (8129/4096:ℝ) with hc | hc
          · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
            have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
            have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_359 (x + y) (by linarith) (by linarith)
            have hw4 : (5774823/625000000000:ℝ) ≤ wfun (y + z) := wc_480 (y + z) (by linarith) (by linarith)
            have hw5 : (242372143/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_924 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
            have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
            have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_374 (x + y) (by linarith) (by linarith)
            have hw4 : (569617/50000000000:ℝ) ≤ wfun (y + z) := wc_507 (y + z) (by linarith) (by linarith)
            have hw5 : (1265836939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_947 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (8129/4096:ℝ) with hc | hc
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · rcases le_total x (8519/8192:ℝ) with hc | hc
              · have hw0 : (482068367/2000000000000:ℝ) ≤ wfun x := wc_26 x (by linarith) (by linarith)
                have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                have hw3 : (4662827/10000000000000:ℝ) ≤ wfun (x + y) := wc_373 (x + y) (by linarith) (by linarith)
                have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_479 (y + z) (by linarith) (by linarith)
                have hw5 : (634060693/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_945 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_28 x (by linarith) (by linarith)
                have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                have hw3 : (7258139/10000000000000:ℝ) ≤ wfun (x + y) := wc_380 (x + y) (by linarith) (by linarith)
                have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_479 (y + z) (by linarith) (by linarith)
                have hw5 : (647786457/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_955 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
              have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
              have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_374 (x + y) (by linarith) (by linarith)
              have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_506 (y + z) (by linarith) (by linarith)
              have hw5 : (52900211/400000000000:ℝ) ≤ wfun (x + y + z) := wc_966 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
              have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
              have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_387 (x + y) (by linarith) (by linarith)
              have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_506 (y + z) (by linarith) (by linarith)
              have hw5 : (52900211/400000000000:ℝ) ≤ wfun (x + y + z) := wc_966 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
              have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
              have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_387 (x + y) (by linarith) (by linarith)
              have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
              have hw5 : (275750223/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_990 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (4257/4096:ℝ) with hc | hc
        · rcases le_total y (8129/4096:ℝ) with hc | hc
          · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
            have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
            have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_359 (x + y) (by linarith) (by linarith)
            have hw4 : (4302423/312500000000:ℝ) ≤ wfun (y + z) := wc_516 (y + z) (by linarith) (by linarith)
            have hw5 : (660458559/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_967 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
            have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
            have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_374 (x + y) (by linarith) (by linarith)
            have hw4 : (163652657/10000000000000:ℝ) ≤ wfun (y + z) := wc_524 (y + z) (by linarith) (by linarith)
            have hw5 : (172136989/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_991 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (8129/4096:ℝ) with hc | hc
          · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
            have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
            have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_374 (x + y) (by linarith) (by linarith)
            have hw4 : (4302423/312500000000:ℝ) ≤ wfun (y + z) := wc_516 (y + z) (by linarith) (by linarith)
            have hw5 : (172136989/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_991 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
            have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
            have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_387 (x + y) (by linarith) (by linarith)
            have hw4 : (163652657/10000000000000:ℝ) ≤ wfun (y + z) := wc_524 (y + z) (by linarith) (by linarith)
            have hw5 : (57374717/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1012 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total z (2151/2048:ℝ) with hc | hc
      · rcases le_total x (4257/4096:ℝ) with hc | hc
        · rcases le_total y (8139/4096:ℝ) with hc | hc
          · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
            have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
            have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_387 (x + y) (by linarith) (by linarith)
            have hw4 : (4302423/312500000000:ℝ) ≤ wfun (y + z) := wc_516 (y + z) (by linarith) (by linarith)
            have hw5 : (660458559/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_967 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
            have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
            have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_403 (x + y) (by linarith) (by linarith)
            have hw4 : (163652657/10000000000000:ℝ) ≤ wfun (y + z) := wc_524 (y + z) (by linarith) (by linarith)
            have hw5 : (172136989/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_991 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (8139/4096:ℝ) with hc | hc
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
              have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
              have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_403 (x + y) (by linarith) (by linarith)
              have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
              have hw5 : (275750223/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_990 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
              have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
              have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_403 (x + y) (by linarith) (by linarith)
              have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
              have hw5 : (718045723/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1011 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
              have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
              have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_417 (x + y) (by linarith) (by linarith)
              have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
              have hw5 : (718045723/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1011 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
              have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
              have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_417 (x + y) (by linarith) (by linarith)
              have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_529 (y + z) (by linarith) (by linarith)
              have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1044 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (4257/4096:ℝ) with hc | hc
        · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
          have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_210 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
          have hw3 : (649907/625000000000:ℝ) ≤ wfun (x + y) := wc_388 (x + y) (by linarith) (by linarith)
          have hw4 : (23941523/1250000000000:ℝ) ≤ wfun (y + z) := wc_531 (y + z) (by linarith) (by linarith)
          have hw5 : (1432646991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1013 (x + y + z) (by linarith) (by linarith)
          linarith
        · rcases le_total y (8139/4096:ℝ) with hc | hc
          · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
            have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
            have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_403 (x + y) (by linarith) (by linarith)
            have hw4 : (47960431/2500000000000:ℝ) ≤ wfun (y + z) := wc_530 (y + z) (by linarith) (by linarith)
            have hw5 : (1492727701/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1045 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
            have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
            have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_417 (x + y) (by linarith) (by linarith)
            have hw4 : (111118793/5000000000000:ℝ) ≤ wfun (y + z) := wc_540 (y + z) (by linarith) (by linarith)
            have hw5 : (62086789/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1066 (x + y + z) (by linarith) (by linarith)
            linarith
  · rcases le_total y (4067/2048:ℝ) with hc | hc
    · rcases le_total z (2151/2048:ℝ) with hc | hc
      · rcases le_total x (4267/4096:ℝ) with hc | hc
        · rcases le_total y (8129/4096:ℝ) with hc | hc
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · rcases le_total x (8529/8192:ℝ) with hc | hc
              · have hw0 : (1038927507/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                have hw3 : (5211923/5000000000000:ℝ) ≤ wfun (x + y) := wc_386 (x + y) (by linarith) (by linarith)
                have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_479 (y + z) (by linarith) (by linarith)
                have hw5 : (1323300249/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_965 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total y (16253/8192:ℝ) with hc | hc
                · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_32 x (by linarith) (by linarith)
                  have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                  have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
                  have hw4 : (46310863/5000000000000:ℝ) ≤ wfun (y + z) := wc_478 (y + z) (by linarith) (by linarith)
                  have hw5 : (338028751/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_979 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_32 x (by linarith) (by linarith)
                  have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                  have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
                  have hw4 : (25782839/2500000000000:ℝ) ≤ wfun (y + z) := wc_499 (y + z) (by linarith) (by linarith)
                  have hw5 : (690204403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_988 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total x (8529/8192:ℝ) with hc | hc
              · have hw0 : (1038927507/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                have hw3 : (5211923/5000000000000:ℝ) ≤ wfun (x + y) := wc_386 (x + y) (by linarith) (by linarith)
                have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_506 (y + z) (by linarith) (by linarith)
                have hw5 : (1379579649/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_989 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_32 x (by linarith) (by linarith)
                have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                have hw3 : (3539799/2500000000000:ℝ) ≤ wfun (x + y) := wc_396 (x + y) (by linarith) (by linarith)
                have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_506 (y + z) (by linarith) (by linarith)
                have hw5 : (1408130363/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1001 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · rcases le_total x (8529/8192:ℝ) with hc | hc
              · have hw0 : (1038927507/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                have hw3 : (1846343/1000000000000:ℝ) ≤ wfun (x + y) := wc_402 (x + y) (by linarith) (by linarith)
                have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_506 (y + z) (by linarith) (by linarith)
                have hw5 : (1379579649/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_989 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total y (16263/8192:ℝ) with hc | hc
                · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_32 x (by linarith) (by linarith)
                  have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                  have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_409 (x + y) (by linarith) (by linarith)
                  have hw4 : (114200161/10000000000000:ℝ) ≤ wfun (y + z) := wc_505 (y + z) (by linarith) (by linarith)
                  have hw5 : (176122069/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1000 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_32 x (by linarith) (by linarith)
                  have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                  have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
                  have hw4 : (15728411/1250000000000:ℝ) ≤ wfun (y + z) := wc_511 (y + z) (by linarith) (by linarith)
                  have hw5 : (718908779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1009 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total x (8529/8192:ℝ) with hc | hc
              · have hw0 : (1038927507/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                have hw3 : (1846343/1000000000000:ℝ) ≤ wfun (x + y) := wc_402 (x + y) (by linarith) (by linarith)
                have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
                have hw5 : (718477089/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1010 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_32 x (by linarith) (by linarith)
                have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                have hw3 : (23335779/10000000000000:ℝ) ≤ wfun (x + y) := wc_410 (x + y) (by linarith) (by linarith)
                have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
                have hw5 : (1466050409/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1034 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total y (8129/4096:ℝ) with hc | hc
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · rcases le_total x (8539/8192:ℝ) with hc | hc
              · rcases le_total y (16253/8192:ℝ) with hc | hc
                · have hw0 : (1770787537/10000000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
                  have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                  have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
                  have hw4 : (46310863/5000000000000:ℝ) ≤ wfun (y + z) := wc_478 (y + z) (by linarith) (by linarith)
                  have hw5 : (690204403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_988 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1770787537/10000000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
                  have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                  have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_409 (x + y) (by linarith) (by linarith)
                  have hw4 : (25782839/2500000000000:ℝ) ≤ wfun (y + z) := wc_499 (y + z) (by linarith) (by linarith)
                  have hw5 : (176122069/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1000 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (16253/8192:ℝ) with hc | hc
                · rcases le_total z (8589/8192:ℝ) with hc | hc
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                    have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                    have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                    have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_409 (x + y) (by linarith) (by linarith)
                    have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
                    have hw5 : (1409823377/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_999 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                    have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                    have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                    have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_409 (x + y) (by linarith) (by linarith)
                    have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
                    have hw5 : (1438681587/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1008 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total z (8589/8192:ℝ) with hc | hc
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                    have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                    have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                    have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
                    have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
                    have hw5 : (1438681587/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1008 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                    have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                    have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                    have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
                    have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                    have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
                    linarith
            · rcases le_total x (8539/8192:ℝ) with hc | hc
              · rcases le_total y (16253/8192:ℝ) with hc | hc
                · have hw0 : (1770787537/10000000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
                  have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                  have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                  have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
                  have hw4 : (114200161/10000000000000:ℝ) ≤ wfun (y + z) := wc_505 (y + z) (by linarith) (by linarith)
                  have hw5 : (718908779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1009 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1770787537/10000000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
                  have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                  have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                  have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_409 (x + y) (by linarith) (by linarith)
                  have hw4 : (15728411/1250000000000:ℝ) ≤ wfun (y + z) := wc_511 (y + z) (by linarith) (by linarith)
                  have hw5 : (1466931139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1033 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (16253/8192:ℝ) with hc | hc
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                  have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                  have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                  have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_409 (x + y) (by linarith) (by linarith)
                  have hw4 : (114200161/10000000000000:ℝ) ≤ wfun (y + z) := wc_505 (y + z) (by linarith) (by linarith)
                  have hw5 : (1466931139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1033 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                  have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                  have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                  have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
                  have hw4 : (15728411/1250000000000:ℝ) ≤ wfun (y + z) := wc_511 (y + z) (by linarith) (by linarith)
                  have hw5 : (748158303/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1042 (x + y + z) (by linarith) (by linarith)
                  linarith
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · rcases le_total x (8539/8192:ℝ) with hc | hc
              · rcases le_total y (16263/8192:ℝ) with hc | hc
                · have hw0 : (1770787537/10000000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
                  have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                  have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
                  have hw4 : (114200161/10000000000000:ℝ) ≤ wfun (y + z) := wc_505 (y + z) (by linarith) (by linarith)
                  have hw5 : (718908779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1009 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1770787537/10000000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
                  have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                  have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_427 (x + y) (by linarith) (by linarith)
                  have hw4 : (15728411/1250000000000:ℝ) ≤ wfun (y + z) := wc_511 (y + z) (by linarith) (by linarith)
                  have hw5 : (1466931139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1033 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (16263/8192:ℝ) with hc | hc
                · rcases le_total z (8589/8192:ℝ) with hc | hc
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                    have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                    have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                    have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_427 (x + y) (by linarith) (by linarith)
                    have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                    have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                    have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                    have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                    have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_427 (x + y) (by linarith) (by linarith)
                    have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
                    have hw5 : (748607759/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1041 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total z (8589/8192:ℝ) with hc | hc
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                    have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
                    have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                    have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_433 (x + y) (by linarith) (by linarith)
                    have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
                    have hw5 : (748607759/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1041 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                    have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
                    have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                    have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_433 (x + y) (by linarith) (by linarith)
                    have hw4 : (6906177/500000000000:ℝ) ≤ wfun (y + z) := wc_513 (y + z) (by linarith) (by linarith)
                    have hw5 : (11928827/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1053 (x + y + z) (by linarith) (by linarith)
                    linarith
            · rcases le_total x (8539/8192:ℝ) with hc | hc
              · rcases le_total y (16263/8192:ℝ) with hc | hc
                · have hw0 : (1770787537/10000000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
                  have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                  have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                  have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
                  have hw4 : (138011869/10000000000000:ℝ) ≤ wfun (y + z) := wc_514 (y + z) (by linarith) (by linarith)
                  have hw5 : (748158303/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1042 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1770787537/10000000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
                  have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
                  have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                  have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_427 (x + y) (by linarith) (by linarith)
                  have hw4 : (30150607/2000000000000:ℝ) ≤ wfun (y + z) := wc_520 (y + z) (by linarith) (by linarith)
                  have hw5 : (305194653/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1054 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (16263/8192:ℝ) with hc | hc
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                  have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                  have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                  have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_427 (x + y) (by linarith) (by linarith)
                  have hw4 : (138011869/10000000000000:ℝ) ≤ wfun (y + z) := wc_514 (y + z) (by linarith) (by linarith)
                  have hw5 : (305194653/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1054 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                  have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
                  have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                  have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_433 (x + y) (by linarith) (by linarith)
                  have hw4 : (30150607/2000000000000:ℝ) ≤ wfun (y + z) := wc_520 (y + z) (by linarith) (by linarith)
                  have hw5 : (77795021/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1063 (x + y + z) (by linarith) (by linarith)
                  linarith
      · rcases le_total x (4267/4096:ℝ) with hc | hc
        · rcases le_total y (8129/4096:ℝ) with hc | hc
          · rcases le_total z (4307/4096:ℝ) with hc | hc
            · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
              have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
              have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_387 (x + y) (by linarith) (by linarith)
              have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
              have hw5 : (718045723/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1011 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
              have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
              have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_387 (x + y) (by linarith) (by linarith)
              have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
              have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1044 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (4307/4096:ℝ) with hc | hc
            · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
              have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
              have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_403 (x + y) (by linarith) (by linarith)
              have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
              have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1044 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
              have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
              have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_403 (x + y) (by linarith) (by linarith)
              have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_529 (y + z) (by linarith) (by linarith)
              have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1065 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (8129/4096:ℝ) with hc | hc
          · rcases le_total z (4307/4096:ℝ) with hc | hc
            · rcases le_total x (8539/8192:ℝ) with hc | hc
              · have hw0 : (1770787537/10000000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
                have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
                have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
                have hw3 : (1846343/1000000000000:ℝ) ≤ wfun (x + y) := wc_402 (x + y) (by linarith) (by linarith)
                have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
                have hw5 : (1495418369/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1043 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
                have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
                have hw3 : (23335779/10000000000000:ℝ) ≤ wfun (x + y) := wc_410 (x + y) (by linarith) (by linarith)
                have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
                have hw5 : (1525057363/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1055 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
              have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
              have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_403 (x + y) (by linarith) (by linarith)
              have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
              have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1065 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (4307/4096:ℝ) with hc | hc
            · rcases le_total x (8539/8192:ℝ) with hc | hc
              · have hw0 : (1770787537/10000000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
                have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
                have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
                have hw3 : (28775469/10000000000000:ℝ) ≤ wfun (x + y) := wc_416 (x + y) (by linarith) (by linarith)
                have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
                have hw5 : (194370837/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1064 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
                have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
                have hw3 : (6956343/2000000000000:ℝ) ≤ wfun (x + y) := wc_428 (x + y) (by linarith) (by linarith)
                have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
                have hw5 : (1585145671/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1078 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
              have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
              have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_417 (x + y) (by linarith) (by linarith)
              have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_529 (y + z) (by linarith) (by linarith)
              have hw5 : (807312237/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1086 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total z (2151/2048:ℝ) with hc | hc
      · rcases le_total x (4267/4096:ℝ) with hc | hc
        · rcases le_total y (8139/4096:ℝ) with hc | hc
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · rcases le_total x (8529/8192:ℝ) with hc | hc
              · have hw0 : (1038927507/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                have hw3 : (28775469/10000000000000:ℝ) ≤ wfun (x + y) := wc_416 (x + y) (by linarith) (by linarith)
                have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
                have hw5 : (718477089/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1010 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_32 x (by linarith) (by linarith)
                have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                have hw3 : (6956343/2000000000000:ℝ) ≤ wfun (x + y) := wc_428 (x + y) (by linarith) (by linarith)
                have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
                have hw5 : (1466050409/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1034 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (8529/8192:ℝ) with hc | hc
              · have hw0 : (1038927507/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                have hw3 : (28775469/10000000000000:ℝ) ≤ wfun (x + y) := wc_416 (x + y) (by linarith) (by linarith)
                have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
                have hw5 : (1495418369/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1043 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_32 x (by linarith) (by linarith)
                have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                have hw3 : (6956343/2000000000000:ℝ) ≤ wfun (x + y) := wc_428 (x + y) (by linarith) (by linarith)
                have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
                have hw5 : (1525057363/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1055 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · rcases le_total x (8529/8192:ℝ) with hc | hc
              · have hw0 : (1038927507/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                have hw3 : (4135373/1000000000000:ℝ) ≤ wfun (x + y) := wc_434 (x + y) (by linarith) (by linarith)
                have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
                have hw5 : (1495418369/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1043 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_32 x (by linarith) (by linarith)
                have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                have hw3 : (48490713/10000000000000:ℝ) ≤ wfun (x + y) := wc_442 (x + y) (by linarith) (by linarith)
                have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
                have hw5 : (1525057363/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1055 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
              have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
              have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_435 (x + y) (by linarith) (by linarith)
              have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_529 (y + z) (by linarith) (by linarith)
              have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1065 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (8139/4096:ℝ) with hc | hc
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · rcases le_total x (8539/8192:ℝ) with hc | hc
              · rcases le_total y (16273/8192:ℝ) with hc | hc
                · have hw0 : (1770787537/10000000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
                  have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                  have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_433 (x + y) (by linarith) (by linarith)
                  have hw4 : (138011869/10000000000000:ℝ) ≤ wfun (y + z) := wc_514 (y + z) (by linarith) (by linarith)
                  have hw5 : (748158303/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1042 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1770787537/10000000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
                  have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                  have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_441 (x + y) (by linarith) (by linarith)
                  have hw4 : (30150607/2000000000000:ℝ) ≤ wfun (y + z) := wc_520 (y + z) (by linarith) (by linarith)
                  have hw5 : (305194653/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1054 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (16273/8192:ℝ) with hc | hc
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                  have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                  have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_441 (x + y) (by linarith) (by linarith)
                  have hw4 : (138011869/10000000000000:ℝ) ≤ wfun (y + z) := wc_514 (y + z) (by linarith) (by linarith)
                  have hw5 : (305194653/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1054 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                  have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                  have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
                  have hw4 : (30150607/2000000000000:ℝ) ≤ wfun (y + z) := wc_520 (y + z) (by linarith) (by linarith)
                  have hw5 : (77795021/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1063 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total x (8539/8192:ℝ) with hc | hc
              · have hw0 : (1770787537/10000000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
                have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                have hw3 : (4135373/1000000000000:ℝ) ≤ wfun (x + y) := wc_434 (x + y) (by linarith) (by linarith)
                have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
                have hw5 : (194370837/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1064 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total y (16273/8192:ℝ) with hc | hc
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                  have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                  have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                  have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_441 (x + y) (by linarith) (by linarith)
                  have hw4 : (82024953/5000000000000:ℝ) ≤ wfun (y + z) := wc_522 (y + z) (by linarith) (by linarith)
                  have hw5 : (793048687/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1077 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                  have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                  have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                  have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
                  have hw4 : (35580319/2000000000000:ℝ) ≤ wfun (y + z) := wc_526 (y + z) (by linarith) (by linarith)
                  have hw5 : (1616563421/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1084 (x + y + z) (by linarith) (by linarith)
                  linarith
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · rcases le_total x (8539/8192:ℝ) with hc | hc
              · have hw0 : (1770787537/10000000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
                have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                have hw3 : (2809593/500000000000:ℝ) ≤ wfun (x + y) := wc_448 (x + y) (by linarith) (by linarith)
                have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
                have hw5 : (194370837/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1064 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total y (16283/8192:ℝ) with hc | hc
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                  have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                  have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
                  have hw4 : (82024953/5000000000000:ℝ) ≤ wfun (y + z) := wc_522 (y + z) (by linarith) (by linarith)
                  have hw5 : (793048687/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1077 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                  have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                  have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
                  have hw4 : (35580319/2000000000000:ℝ) ≤ wfun (y + z) := wc_526 (y + z) (by linarith) (by linarith)
                  have hw5 : (1616563421/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1084 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total x (8539/8192:ℝ) with hc | hc
              · have hw0 : (1770787537/10000000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
                have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                have hw3 : (2809593/500000000000:ℝ) ≤ wfun (x + y) := wc_448 (x + y) (by linarith) (by linarith)
                have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_529 (y + z) (by linarith) (by linarith)
                have hw5 : (100974599/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1085 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                have hw3 : (64456359/10000000000000:ℝ) ≤ wfun (x + y) := wc_458 (x + y) (by linarith) (by linarith)
                have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_529 (y + z) (by linarith) (by linarith)
                have hw5 : (51447179/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1095 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total x (4267/4096:ℝ) with hc | hc
        · rcases le_total y (8139/4096:ℝ) with hc | hc
          · rcases le_total z (4307/4096:ℝ) with hc | hc
            · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
              have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
              have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_417 (x + y) (by linarith) (by linarith)
              have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_529 (y + z) (by linarith) (by linarith)
              have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1065 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
              have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
              have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_417 (x + y) (by linarith) (by linarith)
              have hw4 : (890387/40000000000:ℝ) ≤ wfun (y + z) := wc_539 (y + z) (by linarith) (by linarith)
              have hw5 : (807312237/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1086 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
            have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
            have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_435 (x + y) (by linarith) (by linarith)
            have hw4 : (111118793/5000000000000:ℝ) ≤ wfun (y + z) := wc_540 (y + z) (by linarith) (by linarith)
            have hw5 : (322537687/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1087 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (8139/4096:ℝ) with hc | hc
          · rcases le_total z (4307/4096:ℝ) with hc | hc
            · rcases le_total x (8539/8192:ℝ) with hc | hc
              · have hw0 : (1770787537/10000000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
                have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
                have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
                have hw3 : (4135373/1000000000000:ℝ) ≤ wfun (x + y) := wc_434 (x + y) (by linarith) (by linarith)
                have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_529 (y + z) (by linarith) (by linarith)
                have hw5 : (100974599/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1085 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
                have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
                have hw3 : (48490713/10000000000000:ℝ) ≤ wfun (x + y) := wc_442 (x + y) (by linarith) (by linarith)
                have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_529 (y + z) (by linarith) (by linarith)
                have hw5 : (51447179/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1095 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
              have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
              have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_435 (x + y) (by linarith) (by linarith)
              have hw4 : (890387/40000000000:ℝ) ≤ wfun (y + z) := wc_539 (y + z) (by linarith) (by linarith)
              have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1102 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (4307/4096:ℝ) with hc | hc
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
              have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
              have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_449 (x + y) (by linarith) (by linarith)
              have hw4 : (890387/40000000000:ℝ) ≤ wfun (y + z) := wc_539 (y + z) (by linarith) (by linarith)
              have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1102 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
              have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
              have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_449 (x + y) (by linarith) (by linarith)
              have hw4 : (255244651/10000000000000:ℝ) ≤ wfun (y + z) := wc_542 (y + z) (by linarith) (by linarith)
              have hw5 : (1739017297/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1121 (x + y + z) (by linarith) (by linarith)
              linarith

set_option maxHeartbeats 20000000 in
lemma ch_43 (x y z : ℝ) (hx1 : (267/256:ℝ) ≤ x) (hx2 : x ≤ (1073/1024:ℝ))
    (hy1 : (1013/512:ℝ) ≤ y) (hy2 : y ≤ (2031/1024:ℝ))
    (hz1 : (529/512:ℝ) ≤ z) (hz2 : z ≤ (1063/1024:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (2141/2048:ℝ) with hc | hc
  · rcases le_total y (4057/2048:ℝ) with hc | hc
    · rcases le_total z (2121/2048:ℝ) with hc | hc
      · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
        have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_163 y (by linarith) (by linarith)
        have hw2 : (1888462017/5000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
        have hw3 : (1181561/10000000000000:ℝ) ≤ wfun (x + y) := wc_361 (x + y) (by linarith) (by linarith)
        have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_339 (y + z) (by linarith) (by linarith)
        have hw5 : (162636919/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_820 (x + y + z) (by linarith) (by linarith)
        linarith
      · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
        have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_163 y (by linarith) (by linarith)
        have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
        have hw3 : (1181561/10000000000000:ℝ) ≤ wfun (x + y) := wc_361 (x + y) (by linarith) (by linarith)
        have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_345 (y + z) (by linarith) (by linarith)
        have hw5 : (183045519/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_839 (x + y + z) (by linarith) (by linarith)
        linarith
    · rcases le_total z (2121/2048:ℝ) with hc | hc
      · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
        have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_180 y (by linarith) (by linarith)
        have hw2 : (1888462017/5000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
        have hw3 : (2076333/2000000000000:ℝ) ≤ wfun (x + y) := wc_389 (x + y) (by linarith) (by linarith)
        have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_345 (y + z) (by linarith) (by linarith)
        have hw5 : (183045519/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_839 (x + y + z) (by linarith) (by linarith)
        linarith
      · rcases le_total x (4277/4096:ℝ) with hc | hc
        · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
          have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_180 y (by linarith) (by linarith)
          have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
          have hw3 : (649907/625000000000:ℝ) ≤ wfun (x + y) := wc_388 (x + y) (by linarith) (by linarith)
          have hw5 : (81942717/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_846 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
          have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_180 y (by linarith) (by linarith)
          have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
          have hw3 : (736743/400000000000:ℝ) ≤ wfun (x + y) := wc_404 (x + y) (by linarith) (by linarith)
          have hw5 : (864332647/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_856 (x + y + z) (by linarith) (by linarith)
          linarith
  · rcases le_total y (4057/2048:ℝ) with hc | hc
    · rcases le_total z (2121/2048:ℝ) with hc | hc
      · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_56 x (by linarith) (by linarith)
        have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_163 y (by linarith) (by linarith)
        have hw2 : (1888462017/5000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
        have hw3 : (2076333/2000000000000:ℝ) ≤ wfun (x + y) := wc_389 (x + y) (by linarith) (by linarith)
        have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_339 (y + z) (by linarith) (by linarith)
        have hw5 : (183045519/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_839 (x + y + z) (by linarith) (by linarith)
        linarith
      · rcases le_total x (4287/4096:ℝ) with hc | hc
        · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
          have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_163 y (by linarith) (by linarith)
          have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
          have hw3 : (649907/625000000000:ℝ) ≤ wfun (x + y) := wc_388 (x + y) (by linarith) (by linarith)
          have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_345 (y + z) (by linarith) (by linarith)
          have hw5 : (81942717/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_846 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
          have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_163 y (by linarith) (by linarith)
          have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
          have hw3 : (736743/400000000000:ℝ) ≤ wfun (x + y) := wc_404 (x + y) (by linarith) (by linarith)
          have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_345 (y + z) (by linarith) (by linarith)
          have hw5 : (864332647/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_856 (x + y + z) (by linarith) (by linarith)
          linarith
    · rcases le_total z (2121/2048:ℝ) with hc | hc
      · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_56 x (by linarith) (by linarith)
        have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_180 y (by linarith) (by linarith)
        have hw2 : (1888462017/5000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
        have hw3 : (14329561/5000000000000:ℝ) ≤ wfun (x + y) := wc_419 (x + y) (by linarith) (by linarith)
        have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_345 (y + z) (by linarith) (by linarith)
        have hw5 : (12788137/156250000000:ℝ) ≤ wfun (x + y + z) := wc_847 (x + y + z) (by linarith) (by linarith)
        linarith
      · rcases le_total x (4287/4096:ℝ) with hc | hc
        · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
          have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_180 y (by linarith) (by linarith)
          have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
          have hw3 : (2870559/1000000000000:ℝ) ≤ wfun (x + y) := wc_418 (x + y) (by linarith) (by linarith)
          have hw5 : (910381357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_859 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
          have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_180 y (by linarith) (by linarith)
          have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
          have hw3 : (20626673/5000000000000:ℝ) ≤ wfun (x + y) := wc_436 (x + y) (by linarith) (by linarith)
          have hw5 : (191513687/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_867 (x + y + z) (by linarith) (by linarith)
          linarith

set_option maxHeartbeats 20000000 in
lemma ch_60 (x y z : ℝ) (hx1 : (2141/2048:ℝ) ≤ x) (hx2 : x ≤ (1073/1024:ℝ))
    (hy1 : (4047/2048:ℝ) ≤ y) (hy2 : y ≤ (1013/512:ℝ))
    (hz1 : (267/256:ℝ) ≤ z) (hz2 : z ≤ (2141/2048:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (4287/4096:ℝ) with hc | hc
  · rcases le_total y (8099/4096:ℝ) with hc | hc
    · rcases le_total z (4277/4096:ℝ) with hc | hc
      · rcases le_total x (8569/8192:ℝ) with hc | hc
        · rcases le_total y (16193/8192:ℝ) with hc | hc
          · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
            have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
            have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
            have hw5 : (1009528097/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_869 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
            have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
            have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
            have hw5 : (517100111/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_883 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (16193/8192:ℝ) with hc | hc
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
            have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
            have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
            have hw5 : (517100111/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_883 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
            have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
            have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
            have hw5 : (264788707/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_885 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total x (8569/8192:ℝ) with hc | hc
        · rcases le_total y (16193/8192:ℝ) with hc | hc
          · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
            have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
            have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
            have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_352 (y + z) (by linarith) (by linarith)
            have hw5 : (264788707/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_885 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
              have hw4 : (306931/10000000000000:ℝ) ≤ wfun (y + z) := wc_355 (y + z) (by linarith) (by linarith)
              have hw5 : (1085044203/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_890 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
              have hw4 : (1187329/10000000000000:ℝ) ≤ wfun (y + z) := wc_357 (y + z) (by linarith) (by linarith)
              have hw5 : (555288563/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_893 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16193/8192:ℝ) with hc | hc
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
              have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_351 (y + z) (by linarith) (by linarith)
              have hw5 : (1085044203/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_890 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
              have hw4 : (306931/10000000000000:ℝ) ≤ wfun (y + z) := wc_355 (y + z) (by linarith) (by linarith)
              have hw5 : (555288563/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_893 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
              have hw4 : (306931/10000000000000:ℝ) ≤ wfun (y + z) := wc_355 (y + z) (by linarith) (by linarith)
              have hw5 : (555288563/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_893 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
              have hw4 : (1187329/10000000000000:ℝ) ≤ wfun (y + z) := wc_357 (y + z) (by linarith) (by linarith)
              have hw5 : (1136390777/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_902 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total z (4277/4096:ℝ) with hc | hc
      · rcases le_total x (8569/8192:ℝ) with hc | hc
        · rcases le_total y (16203/8192:ℝ) with hc | hc
          · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
            have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
            have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
            have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_352 (y + z) (by linarith) (by linarith)
            have hw5 : (264788707/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_885 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
              have hw4 : (306931/10000000000000:ℝ) ≤ wfun (y + z) := wc_355 (y + z) (by linarith) (by linarith)
              have hw5 : (1085044203/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_890 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
              have hw4 : (1187329/10000000000000:ℝ) ≤ wfun (y + z) := wc_357 (y + z) (by linarith) (by linarith)
              have hw5 : (555288563/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_893 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16203/8192:ℝ) with hc | hc
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
              have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_351 (y + z) (by linarith) (by linarith)
              have hw5 : (1085044203/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_890 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
              have hw4 : (306931/10000000000000:ℝ) ≤ wfun (y + z) := wc_355 (y + z) (by linarith) (by linarith)
              have hw5 : (555288563/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_893 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
              have hw4 : (306931/10000000000000:ℝ) ≤ wfun (y + z) := wc_355 (y + z) (by linarith) (by linarith)
              have hw5 : (555288563/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_893 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
              have hw4 : (1187329/10000000000000:ℝ) ≤ wfun (y + z) := wc_357 (y + z) (by linarith) (by linarith)
              have hw5 : (1136390777/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_902 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (8569/8192:ℝ) with hc | hc
        · rcases le_total y (16203/8192:ℝ) with hc | hc
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
              have hw4 : (1187329/10000000000000:ℝ) ≤ wfun (y + z) := wc_357 (y + z) (by linarith) (by linarith)
              have hw5 : (555288563/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_893 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
              have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
              have hw5 : (1136390777/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_902 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
              have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
              have hw5 : (1136390777/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_902 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (17133/16384:ℝ) with hc | hc
              · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (7266981/10000000000000:ℝ) ≤ wfun (x + y) := wc_378 (x + y) (by linarith) (by linarith)
                have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
                have hw5 : (1162834311/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_905 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (4390211/5000000000000:ℝ) ≤ wfun (x + y) := wc_382 (x + y) (by linarith) (by linarith)
                have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
                have hw5 : (1175989937/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_912 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total y (16203/8192:ℝ) with hc | hc
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
              have hw4 : (1187329/10000000000000:ℝ) ≤ wfun (y + z) := wc_357 (y + z) (by linarith) (by linarith)
              have hw5 : (1136390777/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_902 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
              have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
              have hw5 : (116248451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_906 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
              have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
              have hw5 : (116248451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_906 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (17143/16384:ℝ) with hc | hc
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (5218271/5000000000000:ℝ) ≤ wfun (x + y) := wc_384 (x + y) (by linarith) (by linarith)
                have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
                have hw5 : (594607679/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_913 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (2447049/2000000000000:ℝ) ≤ wfun (x + y) := wc_392 (x + y) (by linarith) (by linarith)
                have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
                have hw5 : (37578453/312500000000:ℝ) ≤ wfun (x + y + z) := wc_917 (x + y + z) (by linarith) (by linarith)
                linarith
  · rcases le_total y (8099/4096:ℝ) with hc | hc
    · rcases le_total z (4277/4096:ℝ) with hc | hc
      · rcases le_total x (8579/8192:ℝ) with hc | hc
        · rcases le_total y (16193/8192:ℝ) with hc | hc
          · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
            have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
            have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
            have hw5 : (264788707/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_885 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
            have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
            have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
            have hw5 : (13554891/125000000000:ℝ) ≤ wfun (x + y + z) := wc_891 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (16193/8192:ℝ) with hc | hc
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
            have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
            have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
            have hw5 : (13554891/125000000000:ℝ) ≤ wfun (x + y + z) := wc_891 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
            have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
            have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
            have hw5 : (1109908939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_894 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total x (8579/8192:ℝ) with hc | hc
        · rcases le_total y (16193/8192:ℝ) with hc | hc
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
              have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_351 (y + z) (by linarith) (by linarith)
              have hw5 : (555288563/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_893 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
              have hw4 : (306931/10000000000000:ℝ) ≤ wfun (y + z) := wc_355 (y + z) (by linarith) (by linarith)
              have hw5 : (1136390777/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_902 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
              have hw4 : (306931/10000000000000:ℝ) ≤ wfun (y + z) := wc_355 (y + z) (by linarith) (by linarith)
              have hw5 : (1136390777/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_902 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
              have hw4 : (1187329/10000000000000:ℝ) ≤ wfun (y + z) := wc_357 (y + z) (by linarith) (by linarith)
              have hw5 : (116248451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_906 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16193/8192:ℝ) with hc | hc
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
              have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_351 (y + z) (by linarith) (by linarith)
              have hw5 : (1136390777/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_902 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
              have hw4 : (306931/10000000000000:ℝ) ≤ wfun (y + z) := wc_355 (y + z) (by linarith) (by linarith)
              have hw5 : (116248451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_906 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
              have hw4 : (306931/10000000000000:ℝ) ≤ wfun (y + z) := wc_355 (y + z) (by linarith) (by linarith)
              have hw5 : (116248451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_906 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
              have hw4 : (1187329/10000000000000:ℝ) ≤ wfun (y + z) := wc_357 (y + z) (by linarith) (by linarith)
              have hw5 : (47554307/400000000000:ℝ) ≤ wfun (x + y + z) := wc_914 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total z (4277/4096:ℝ) with hc | hc
      · rcases le_total x (8579/8192:ℝ) with hc | hc
        · rcases le_total y (16203/8192:ℝ) with hc | hc
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
              have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_351 (y + z) (by linarith) (by linarith)
              have hw5 : (555288563/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_893 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
              have hw4 : (306931/10000000000000:ℝ) ≤ wfun (y + z) := wc_355 (y + z) (by linarith) (by linarith)
              have hw5 : (1136390777/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_902 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
              have hw4 : (306931/10000000000000:ℝ) ≤ wfun (y + z) := wc_355 (y + z) (by linarith) (by linarith)
              have hw5 : (1136390777/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_902 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
              have hw4 : (1187329/10000000000000:ℝ) ≤ wfun (y + z) := wc_357 (y + z) (by linarith) (by linarith)
              have hw5 : (116248451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_906 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16203/8192:ℝ) with hc | hc
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
              have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_351 (y + z) (by linarith) (by linarith)
              have hw5 : (1136390777/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_902 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
              have hw4 : (306931/10000000000000:ℝ) ≤ wfun (y + z) := wc_355 (y + z) (by linarith) (by linarith)
              have hw5 : (116248451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_906 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
              have hw4 : (306931/10000000000000:ℝ) ≤ wfun (y + z) := wc_355 (y + z) (by linarith) (by linarith)
              have hw5 : (116248451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_906 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
              have hw4 : (1187329/10000000000000:ℝ) ≤ wfun (y + z) := wc_357 (y + z) (by linarith) (by linarith)
              have hw5 : (47554307/400000000000:ℝ) ≤ wfun (x + y + z) := wc_914 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (8579/8192:ℝ) with hc | hc
        · rcases le_total y (16203/8192:ℝ) with hc | hc
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
              have hw4 : (1187329/10000000000000:ℝ) ≤ wfun (y + z) := wc_357 (y + z) (by linarith) (by linarith)
              have hw5 : (116248451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_906 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (17153/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (5218271/5000000000000:ℝ) ≤ wfun (x + y) := wc_384 (x + y) (by linarith) (by linarith)
                have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
                have hw5 : (594607679/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_913 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (2447049/2000000000000:ℝ) ≤ wfun (x + y) := wc_392 (x + y) (by linarith) (by linarith)
                have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
                have hw5 : (37578453/312500000000:ℝ) ≤ wfun (x + y + z) := wc_917 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · rcases le_total x (17153/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (7088219/5000000000000:ℝ) ≤ wfun (x + y) := wc_394 (x + y) (by linarith) (by linarith)
                have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
                have hw5 : (594607679/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_913 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (650401/400000000000:ℝ) ≤ wfun (x + y) := wc_398 (x + y) (by linarith) (by linarith)
                have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
                have hw5 : (37578453/312500000000:ℝ) ≤ wfun (x + y + z) := wc_917 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (17153/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (7088219/5000000000000:ℝ) ≤ wfun (x + y) := wc_394 (x + y) (by linarith) (by linarith)
                have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
                have hw5 : (1215875267/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_919 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (650401/400000000000:ℝ) ≤ wfun (x + y) := wc_398 (x + y) (by linarith) (by linarith)
                have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
                have hw5 : (307327397/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_933 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total y (16203/8192:ℝ) with hc | hc
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
              have hw4 : (1187329/10000000000000:ℝ) ≤ wfun (y + z) := wc_357 (y + z) (by linarith) (by linarith)
              have hw5 : (47554307/400000000000:ℝ) ≤ wfun (x + y + z) := wc_914 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (17163/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (7088219/5000000000000:ℝ) ≤ wfun (x + y) := wc_394 (x + y) (by linarith) (by linarith)
                have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
                have hw5 : (1215875267/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_919 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (650401/400000000000:ℝ) ≤ wfun (x + y) := wc_398 (x + y) (by linarith) (by linarith)
                have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
                have hw5 : (307327397/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_933 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · rcases le_total x (17163/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (18485909/10000000000000:ℝ) ≤ wfun (x + y) := wc_400 (x + y) (by linarith) (by linarith)
                have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
                have hw5 : (1215875267/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_919 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (10426997/5000000000000:ℝ) ≤ wfun (x + y) := wc_406 (x + y) (by linarith) (by linarith)
                have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
                have hw5 : (307327397/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_933 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (17163/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (18485909/10000000000000:ℝ) ≤ wfun (x + y) := wc_400 (x + y) (by linarith) (by linarith)
                have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
                have hw5 : (621406689/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_935 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (10426997/5000000000000:ℝ) ≤ wfun (x + y) := wc_406 (x + y) (by linarith) (by linarith)
                have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
                have hw5 : (628193277/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_940 (x + y + z) (by linarith) (by linarith)
                linarith

set_option maxHeartbeats 20000000 in
lemma ch_69 (x y z : ℝ) (hx1 : (1073/1024:ℝ) ≤ x) (hx2 : x ≤ (539/512:ℝ))
    (hy1 : (63/32:ℝ) ≤ y) (hy2 : y ≤ (2021/1024:ℝ))
    (hz1 : (267/256:ℝ) ≤ z) (hz2 : z ≤ (539/512:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
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
        · rcases le_total x (4297/4096:ℝ) with hc | hc
          · rcases le_total y (8069/4096:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
              have hw1 : (1679250671/2500000000000:ℝ) ≤ wfun y := wc_129 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
              have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_348 (x + y) (by linarith) (by linarith)
              have hw4 : (18318183/10000000000000:ℝ) ≤ wfun (y + z) := wc_338 (y + z) (by linarith) (by linarith)
              have hw5 : (820415059/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_845 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
              have hw1 : (3220913463/5000000000000:ℝ) ≤ wfun y := wc_135 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
              have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_342 (y + z) (by linarith) (by linarith)
              have hw5 : (865374359/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_855 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (8069/4096:ℝ) with hc | hc
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
              have hw1 : (1679250671/2500000000000:ℝ) ≤ wfun y := wc_129 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
              have hw4 : (18318183/10000000000000:ℝ) ≤ wfun (y + z) := wc_338 (y + z) (by linarith) (by linarith)
              have hw5 : (865374359/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_855 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
              have hw1 : (3220913463/5000000000000:ℝ) ≤ wfun y := wc_135 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
              have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_342 (y + z) (by linarith) (by linarith)
              have hw5 : (227869559/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_858 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (4297/4096:ℝ) with hc | hc
          · rcases le_total y (8069/4096:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
              have hw1 : (1679250671/2500000000000:ℝ) ≤ wfun y := wc_129 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
              have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_348 (x + y) (by linarith) (by linarith)
              have hw4 : (906687/2000000000000:ℝ) ≤ wfun (y + z) := wc_344 (y + z) (by linarith) (by linarith)
              have hw5 : (227869559/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_858 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                have hw1 : (3220913463/5000000000000:ℝ) ≤ wfun y := wc_135 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                have hw4 : (906687/2000000000000:ℝ) ≤ wfun (y + z) := wc_346 (y + z) (by linarith) (by linarith)
                have hw5 : (959876941/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_865 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                have hw1 : (3220913463/5000000000000:ℝ) ≤ wfun y := wc_135 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_348 (y + z) (by linarith) (by linarith)
                have hw5 : (126039153/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_871 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (8069/4096:ℝ) with hc | hc
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
              have hw1 : (1679250671/2500000000000:ℝ) ≤ wfun y := wc_129 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
              have hw4 : (906687/2000000000000:ℝ) ≤ wfun (y + z) := wc_344 (y + z) (by linarith) (by linarith)
              have hw5 : (958721819/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_866 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
                have hw1 : (3220913463/5000000000000:ℝ) ≤ wfun y := wc_135 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                have hw4 : (906687/2000000000000:ℝ) ≤ wfun (y + z) := wc_346 (y + z) (by linarith) (by linarith)
                have hw5 : (126039153/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_871 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
                have hw1 : (3220913463/5000000000000:ℝ) ≤ wfun y := wc_135 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_348 (y + z) (by linarith) (by linarith)
                have hw5 : (1057880619/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_887 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total z (2141/2048:ℝ) with hc | hc
        · rcases le_total x (4297/4096:ℝ) with hc | hc
          · rcases le_total y (8079/4096:ℝ) with hc | hc
            · rcases le_total z (4277/4096:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                have hw1 : (6172561523/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_343 (y + z) (by linarith) (by linarith)
                have hw5 : (3564753/39062500000:ℝ) ≤ wfun (x + y + z) := wc_857 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                have hw1 : (6172561523/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw4 : (906687/2000000000000:ℝ) ≤ wfun (y + z) := wc_346 (y + z) (by linarith) (by linarith)
                have hw5 : (959876941/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_865 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (4277/4096:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_139 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_353 (x + y) (by linarith) (by linarith)
                have hw4 : (906687/2000000000000:ℝ) ≤ wfun (y + z) := wc_346 (y + z) (by linarith) (by linarith)
                have hw5 : (959876941/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_865 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_139 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_353 (x + y) (by linarith) (by linarith)
                have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_348 (y + z) (by linarith) (by linarith)
                have hw5 : (126039153/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_871 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (8079/4096:ℝ) with hc | hc
            · rcases le_total z (4277/4096:ℝ) with hc | hc
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
                have hw1 : (6172561523/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_353 (x + y) (by linarith) (by linarith)
                have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_343 (y + z) (by linarith) (by linarith)
                have hw5 : (959876941/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_865 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
                have hw1 : (6172561523/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_353 (x + y) (by linarith) (by linarith)
                have hw4 : (906687/2000000000000:ℝ) ≤ wfun (y + z) := wc_346 (y + z) (by linarith) (by linarith)
                have hw5 : (126039153/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_871 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (4277/4096:ℝ) with hc | hc
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
                have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_139 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_359 (x + y) (by linarith) (by linarith)
                have hw4 : (906687/2000000000000:ℝ) ≤ wfun (y + z) := wc_346 (y + z) (by linarith) (by linarith)
                have hw5 : (126039153/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_871 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
                have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_139 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_359 (x + y) (by linarith) (by linarith)
                have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_348 (y + z) (by linarith) (by linarith)
                have hw5 : (1057880619/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_887 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (4297/4096:ℝ) with hc | hc
          · rcases le_total y (8079/4096:ℝ) with hc | hc
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                have hw1 : (6172561523/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_348 (y + z) (by linarith) (by linarith)
                have hw5 : (126039153/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_871 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                have hw1 : (6172561523/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                have hw5 : (1057880619/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_887 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · rcases le_total x (8589/8192:ℝ) with hc | hc
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                  have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_139 y (by linarith) (by linarith)
                  have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                  have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_352 (x + y) (by linarith) (by linarith)
                  have hw5 : (264629371/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_886 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                  have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_139 y (by linarith) (by linarith)
                  have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                  have hw3 : (153341/5000000000000:ℝ) ≤ wfun (x + y) := wc_356 (x + y) (by linarith) (by linarith)
                  have hw5 : (33866839/312500000000:ℝ) ≤ wfun (x + y + z) := wc_892 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total x (8589/8192:ℝ) with hc | hc
                · rcases le_total y (16163/8192:ℝ) with hc | hc
                  · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                    have hw1 : (6042972143/10000000000000:ℝ) ≤ wfun y := wc_138 y (by linarith) (by linarith)
                    have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                    have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_351 (x + y) (by linarith) (by linarith)
                    have hw5 : (1109908939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_894 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                    have hw1 : (5911934001/10000000000000:ℝ) ≤ wfun y := wc_140 y (by linarith) (by linarith)
                    have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                    have hw3 : (306931/10000000000000:ℝ) ≤ wfun (x + y) := wc_355 (x + y) (by linarith) (by linarith)
                    have hw5 : (567853581/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_903 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total y (16163/8192:ℝ) with hc | hc
                  · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                    have hw1 : (6042972143/10000000000000:ℝ) ≤ wfun y := wc_138 y (by linarith) (by linarith)
                    have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                    have hw3 : (306931/10000000000000:ℝ) ≤ wfun (x + y) := wc_355 (x + y) (by linarith) (by linarith)
                    have hw5 : (567853581/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_903 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                    have hw1 : (5911934001/10000000000000:ℝ) ≤ wfun y := wc_140 y (by linarith) (by linarith)
                    have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                    have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
                    have hw5 : (145223163/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_907 (x + y + z) (by linarith) (by linarith)
                    linarith
          · rcases le_total y (8079/4096:ℝ) with hc | hc
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
                have hw1 : (6172561523/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_353 (x + y) (by linarith) (by linarith)
                have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_348 (y + z) (by linarith) (by linarith)
                have hw5 : (1057880619/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_887 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
                have hw1 : (6172561523/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_353 (x + y) (by linarith) (by linarith)
                have hw5 : (1108574073/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_896 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · rcases le_total x (8599/8192:ℝ) with hc | hc
                · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
                  have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_139 y (by linarith) (by linarith)
                  have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                  have hw3 : (593183/5000000000000:ℝ) ≤ wfun (x + y) := wc_358 (x + y) (by linarith) (by linarith)
                  have hw5 : (554620627/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_895 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
                  have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_139 y (by linarith) (by linarith)
                  have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                  have hw3 : (2638657/10000000000000:ℝ) ≤ wfun (x + y) := wc_369 (x + y) (by linarith) (by linarith)
                  have hw5 : (1135024061/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_904 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total x (8599/8192:ℝ) with hc | hc
                · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
                  have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_139 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                  have hw3 : (593183/5000000000000:ℝ) ≤ wfun (x + y) := wc_358 (x + y) (by linarith) (by linarith)
                  have hw5 : (36283957/312500000000:ℝ) ≤ wfun (x + y + z) := wc_908 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
                  have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_139 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                  have hw3 : (2638657/10000000000000:ℝ) ≤ wfun (x + y) := wc_369 (x + y) (by linarith) (by linarith)
                  have hw5 : (118742829/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_916 (x + y + z) (by linarith) (by linarith)
                  linarith
    · rcases le_total y (4037/2048:ℝ) with hc | hc
      · rcases le_total z (2141/2048:ℝ) with hc | hc
        · rcases le_total x (4307/4096:ℝ) with hc | hc
          · rcases le_total y (8069/4096:ℝ) with hc | hc
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
              have hw1 : (1679250671/2500000000000:ℝ) ≤ wfun y := wc_129 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
              have hw4 : (18318183/10000000000000:ℝ) ≤ wfun (y + z) := wc_338 (y + z) (by linarith) (by linarith)
              have hw5 : (227869559/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_858 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
              have hw1 : (3220913463/5000000000000:ℝ) ≤ wfun y := wc_135 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_353 (x + y) (by linarith) (by linarith)
              have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_342 (y + z) (by linarith) (by linarith)
              have hw5 : (958721819/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_866 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
            have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_130 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
            have hw3 : (41/1250000000000:ℝ) ≤ wfun (x + y) := wc_354 (x + y) (by linarith) (by linarith)
            have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_339 (y + z) (by linarith) (by linarith)
            have hw5 : (191513687/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_867 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total x (4307/4096:ℝ) with hc | hc
          · rcases le_total y (8069/4096:ℝ) with hc | hc
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
              have hw1 : (1679250671/2500000000000:ℝ) ≤ wfun y := wc_129 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
              have hw4 : (906687/2000000000000:ℝ) ≤ wfun (y + z) := wc_344 (y + z) (by linarith) (by linarith)
              have hw5 : (1007100179/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_872 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
              have hw1 : (3220913463/5000000000000:ℝ) ≤ wfun y := wc_135 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_353 (x + y) (by linarith) (by linarith)
              have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_347 (y + z) (by linarith) (by linarith)
              have hw5 : (528304163/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_888 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (8069/4096:ℝ) with hc | hc
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
              have hw1 : (1679250671/2500000000000:ℝ) ≤ wfun y := wc_129 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_353 (x + y) (by linarith) (by linarith)
              have hw4 : (906687/2000000000000:ℝ) ≤ wfun (y + z) := wc_344 (y + z) (by linarith) (by linarith)
              have hw5 : (528304163/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_888 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
              have hw1 : (3220913463/5000000000000:ℝ) ≤ wfun y := wc_135 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
              have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_359 (x + y) (by linarith) (by linarith)
              have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_347 (y + z) (by linarith) (by linarith)
              have hw5 : (553620607/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_897 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (2141/2048:ℝ) with hc | hc
        · rcases le_total x (4307/4096:ℝ) with hc | hc
          · rcases le_total y (8079/4096:ℝ) with hc | hc
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
              have hw1 : (6172561523/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
              have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_359 (x + y) (by linarith) (by linarith)
              have hw4 : (906687/2000000000000:ℝ) ≤ wfun (y + z) := wc_344 (y + z) (by linarith) (by linarith)
              have hw5 : (1007100179/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_872 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (4277/4096:ℝ) with hc | hc
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
                have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_139 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_374 (x + y) (by linarith) (by linarith)
                have hw4 : (906687/2000000000000:ℝ) ≤ wfun (y + z) := wc_346 (y + z) (by linarith) (by linarith)
                have hw5 : (1057880619/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_887 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
                have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_139 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_374 (x + y) (by linarith) (by linarith)
                have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_348 (y + z) (by linarith) (by linarith)
                have hw5 : (1108574073/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_896 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (8079/4096:ℝ) with hc | hc
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
              have hw1 : (6172561523/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
              have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_374 (x + y) (by linarith) (by linarith)
              have hw4 : (906687/2000000000000:ℝ) ≤ wfun (y + z) := wc_344 (y + z) (by linarith) (by linarith)
              have hw5 : (528304163/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_888 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (4277/4096:ℝ) with hc | hc
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
                have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_139 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_387 (x + y) (by linarith) (by linarith)
                have hw4 : (906687/2000000000000:ℝ) ≤ wfun (y + z) := wc_346 (y + z) (by linarith) (by linarith)
                have hw5 : (1108574073/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_896 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
                have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_139 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_387 (x + y) (by linarith) (by linarith)
                have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_348 (y + z) (by linarith) (by linarith)
                have hw5 : (290097117/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_909 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (4307/4096:ℝ) with hc | hc
          · rcases le_total y (8079/4096:ℝ) with hc | hc
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
                have hw1 : (6172561523/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_359 (x + y) (by linarith) (by linarith)
                have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_348 (y + z) (by linarith) (by linarith)
                have hw5 : (1108574073/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_896 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
                have hw1 : (6172561523/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_359 (x + y) (by linarith) (by linarith)
                have hw5 : (290097117/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_909 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
                have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_139 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_374 (x + y) (by linarith) (by linarith)
                have hw5 : (290097117/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_909 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total x (8609/8192:ℝ) with hc | hc
                · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                  have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_139 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                  have hw3 : (4662827/10000000000000:ℝ) ≤ wfun (x + y) := wc_373 (x + y) (by linarith) (by linarith)
                  have hw5 : (303512103/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_922 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                  have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_139 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                  have hw3 : (7258139/10000000000000:ℝ) ≤ wfun (x + y) := wc_380 (x + y) (by linarith) (by linarith)
                  have hw5 : (124094633/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_938 (x + y + z) (by linarith) (by linarith)
                  linarith
          · rcases le_total y (8079/4096:ℝ) with hc | hc
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
                have hw1 : (6172561523/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_374 (x + y) (by linarith) (by linarith)
                have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_348 (y + z) (by linarith) (by linarith)
                have hw5 : (290097117/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_909 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
                have hw1 : (6172561523/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_374 (x + y) (by linarith) (by linarith)
                have hw5 : (1213318631/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_923 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
                have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_139 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_387 (x + y) (by linarith) (by linarith)
                have hw5 : (1213318631/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_923 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
                have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_139 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_387 (x + y) (by linarith) (by linarith)
                have hw5 : (1267359331/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_946 (x + y + z) (by linarith) (by linarith)
                linarith
  · rcases le_total x (2151/2048:ℝ) with hc | hc
    · rcases le_total y (4037/2048:ℝ) with hc | hc
      · rcases le_total z (2151/2048:ℝ) with hc | hc
        · rcases le_total x (4297/4096:ℝ) with hc | hc
          · rcases le_total y (8069/4096:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
              have hw1 : (1679250671/2500000000000:ℝ) ≤ wfun y := wc_129 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
              have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_348 (x + y) (by linarith) (by linarith)
              have hw5 : (1007100179/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_872 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (4297/4096:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                have hw1 : (3220913463/5000000000000:ℝ) ≤ wfun y := wc_135 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                have hw5 : (1057880619/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_887 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                have hw1 : (3220913463/5000000000000:ℝ) ≤ wfun y := wc_135 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                have hw5 : (1108574073/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_896 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (8069/4096:ℝ) with hc | hc
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
              have hw1 : (1679250671/2500000000000:ℝ) ≤ wfun y := wc_129 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
              have hw5 : (528304163/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_888 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (4297/4096:ℝ) with hc | hc
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
                have hw1 : (3220913463/5000000000000:ℝ) ≤ wfun y := wc_135 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                have hw5 : (1108574073/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_896 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
                have hw1 : (3220913463/5000000000000:ℝ) ≤ wfun y := wc_135 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                have hw5 : (290097117/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_909 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (4297/4096:ℝ) with hc | hc
          · rcases le_total y (8069/4096:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
              have hw1 : (1679250671/2500000000000:ℝ) ≤ wfun y := wc_129 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
              have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_348 (x + y) (by linarith) (by linarith)
              have hw5 : (553620607/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_897 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
              have hw1 : (3220913463/5000000000000:ℝ) ≤ wfun y := wc_135 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
              have hw4 : (41/1250000000000:ℝ) ≤ wfun (y + z) := wc_354 (y + z) (by linarith) (by linarith)
              have hw5 : (1158993733/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_910 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (8069/4096:ℝ) with hc | hc
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
              have hw1 : (1679250671/2500000000000:ℝ) ≤ wfun y := wc_129 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
              have hw5 : (1158993733/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_910 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
              have hw1 : (3220913463/5000000000000:ℝ) ≤ wfun y := wc_135 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
              have hw4 : (41/1250000000000:ℝ) ≤ wfun (y + z) := wc_354 (y + z) (by linarith) (by linarith)
              have hw5 : (242372143/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_924 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (2151/2048:ℝ) with hc | hc
        · rcases le_total x (4297/4096:ℝ) with hc | hc
          · rcases le_total y (8079/4096:ℝ) with hc | hc
            · rcases le_total z (4297/4096:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                have hw1 : (6172561523/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                have hw5 : (1108574073/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_896 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                have hw1 : (6172561523/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_353 (y + z) (by linarith) (by linarith)
                have hw5 : (290097117/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_909 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (4297/4096:ℝ) with hc | hc
              · rcases le_total x (8589/8192:ℝ) with hc | hc
                · rcases le_total y (16163/8192:ℝ) with hc | hc
                  · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                    have hw1 : (6042972143/10000000000000:ℝ) ≤ wfun y := wc_138 y (by linarith) (by linarith)
                    have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                    have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_351 (x + y) (by linarith) (by linarith)
                    have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_352 (y + z) (by linarith) (by linarith)
                    have hw5 : (145223163/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_907 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                    have hw1 : (5911934001/10000000000000:ℝ) ≤ wfun y := wc_140 y (by linarith) (by linarith)
                    have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                    have hw3 : (306931/10000000000000:ℝ) ≤ wfun (x + y) := wc_355 (x + y) (by linarith) (by linarith)
                    have hw4 : (153341/5000000000000:ℝ) ≤ wfun (y + z) := wc_356 (y + z) (by linarith) (by linarith)
                    have hw5 : (594071357/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_915 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total y (16163/8192:ℝ) with hc | hc
                  · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                    have hw1 : (6042972143/10000000000000:ℝ) ≤ wfun y := wc_138 y (by linarith) (by linarith)
                    have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                    have hw3 : (306931/10000000000000:ℝ) ≤ wfun (x + y) := wc_355 (x + y) (by linarith) (by linarith)
                    have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_352 (y + z) (by linarith) (by linarith)
                    have hw5 : (594071357/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_915 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                    have hw1 : (5911934001/10000000000000:ℝ) ≤ wfun y := wc_140 y (by linarith) (by linarith)
                    have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                    have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
                    have hw4 : (153341/5000000000000:ℝ) ≤ wfun (y + z) := wc_356 (y + z) (by linarith) (by linarith)
                    have hw5 : (1214778741/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_921 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total x (8589/8192:ℝ) with hc | hc
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                  have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_139 y (by linarith) (by linarith)
                  have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                  have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_352 (x + y) (by linarith) (by linarith)
                  have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_359 (y + z) (by linarith) (by linarith)
                  have hw5 : (303512103/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_922 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                  have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_139 y (by linarith) (by linarith)
                  have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                  have hw3 : (153341/5000000000000:ℝ) ≤ wfun (x + y) := wc_356 (x + y) (by linarith) (by linarith)
                  have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_359 (y + z) (by linarith) (by linarith)
                  have hw5 : (124094633/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_938 (x + y + z) (by linarith) (by linarith)
                  linarith
          · rcases le_total y (8079/4096:ℝ) with hc | hc
            · rcases le_total z (4297/4096:ℝ) with hc | hc
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
                have hw1 : (6172561523/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_353 (x + y) (by linarith) (by linarith)
                have hw5 : (290097117/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_909 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
                have hw1 : (6172561523/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_353 (x + y) (by linarith) (by linarith)
                have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_353 (y + z) (by linarith) (by linarith)
                have hw5 : (1213318631/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_923 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (4297/4096:ℝ) with hc | hc
              · rcases le_total x (8599/8192:ℝ) with hc | hc
                · rcases le_total y (16163/8192:ℝ) with hc | hc
                  · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
                    have hw1 : (6042972143/10000000000000:ℝ) ≤ wfun y := wc_138 y (by linarith) (by linarith)
                    have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                    have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
                    have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_352 (y + z) (by linarith) (by linarith)
                    have hw5 : (1214778741/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_921 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
                    have hw1 : (5911934001/10000000000000:ℝ) ≤ wfun y := wc_140 y (by linarith) (by linarith)
                    have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                    have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
                    have hw4 : (153341/5000000000000:ℝ) ≤ wfun (y + z) := wc_356 (y + z) (by linarith) (by linarith)
                    have hw5 : (155211591/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_937 (x + y + z) (by linarith) (by linarith)
                    linarith
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
                  have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_139 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                  have hw3 : (2638657/10000000000000:ℝ) ≤ wfun (x + y) := wc_369 (x + y) (by linarith) (by linarith)
                  have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_353 (y + z) (by linarith) (by linarith)
                  have hw5 : (124094633/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_938 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total x (8599/8192:ℝ) with hc | hc
                · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
                  have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_139 y (by linarith) (by linarith)
                  have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                  have hw3 : (593183/5000000000000:ℝ) ≤ wfun (x + y) := wc_358 (x + y) (by linarith) (by linarith)
                  have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_359 (y + z) (by linarith) (by linarith)
                  have hw5 : (634060693/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_945 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
                  have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_139 y (by linarith) (by linarith)
                  have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                  have hw3 : (2638657/10000000000000:ℝ) ≤ wfun (x + y) := wc_369 (x + y) (by linarith) (by linarith)
                  have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_359 (y + z) (by linarith) (by linarith)
                  have hw5 : (647786457/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_955 (x + y + z) (by linarith) (by linarith)
                  linarith
        · rcases le_total x (4297/4096:ℝ) with hc | hc
          · rcases le_total y (8079/4096:ℝ) with hc | hc
            · rcases le_total z (4307/4096:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                have hw1 : (6172561523/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
                have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_359 (y + z) (by linarith) (by linarith)
                have hw5 : (1213318631/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_923 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                have hw1 : (6172561523/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
                have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_374 (y + z) (by linarith) (by linarith)
                have hw5 : (1267359331/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_946 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (4307/4096:ℝ) with hc | hc
              · rcases le_total x (8589/8192:ℝ) with hc | hc
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                  have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_139 y (by linarith) (by linarith)
                  have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
                  have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_352 (x + y) (by linarith) (by linarith)
                  have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_374 (y + z) (by linarith) (by linarith)
                  have hw5 : (634060693/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_945 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                  have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_139 y (by linarith) (by linarith)
                  have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
                  have hw3 : (153341/5000000000000:ℝ) ≤ wfun (x + y) := wc_356 (x + y) (by linarith) (by linarith)
                  have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_374 (y + z) (by linarith) (by linarith)
                  have hw5 : (647786457/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_955 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_139 y (by linarith) (by linarith)
                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
                have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_353 (x + y) (by linarith) (by linarith)
                have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_387 (y + z) (by linarith) (by linarith)
                have hw5 : (52900211/400000000000:ℝ) ≤ wfun (x + y + z) := wc_966 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (8079/4096:ℝ) with hc | hc
            · rcases le_total z (4307/4096:ℝ) with hc | hc
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
                have hw1 : (6172561523/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
                have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_353 (x + y) (by linarith) (by linarith)
                have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_359 (y + z) (by linarith) (by linarith)
                have hw5 : (1267359331/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_946 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
                have hw1 : (6172561523/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
                have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_353 (x + y) (by linarith) (by linarith)
                have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_374 (y + z) (by linarith) (by linarith)
                have hw5 : (52900211/400000000000:ℝ) ≤ wfun (x + y + z) := wc_966 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (4307/4096:ℝ) with hc | hc
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
                have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_139 y (by linarith) (by linarith)
                have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
                have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_359 (x + y) (by linarith) (by linarith)
                have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_374 (y + z) (by linarith) (by linarith)
                have hw5 : (52900211/400000000000:ℝ) ≤ wfun (x + y + z) := wc_966 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
                have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_139 y (by linarith) (by linarith)
                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
                have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_359 (x + y) (by linarith) (by linarith)
                have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_387 (y + z) (by linarith) (by linarith)
                have hw5 : (275750223/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_990 (x + y + z) (by linarith) (by linarith)
                linarith
    · rcases le_total y (4037/2048:ℝ) with hc | hc
      · rcases le_total z (2151/2048:ℝ) with hc | hc
        · rcases le_total x (4307/4096:ℝ) with hc | hc
          · rcases le_total y (8069/4096:ℝ) with hc | hc
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
              have hw1 : (1679250671/2500000000000:ℝ) ≤ wfun y := wc_129 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
              have hw5 : (553620607/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_897 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
              have hw1 : (3220913463/5000000000000:ℝ) ≤ wfun y := wc_135 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_353 (x + y) (by linarith) (by linarith)
              have hw5 : (1158993733/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_910 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (8069/4096:ℝ) with hc | hc
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
              have hw1 : (1679250671/2500000000000:ℝ) ≤ wfun y := wc_129 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_353 (x + y) (by linarith) (by linarith)
              have hw5 : (1158993733/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_910 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
              have hw1 : (3220913463/5000000000000:ℝ) ≤ wfun y := wc_135 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
              have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_359 (x + y) (by linarith) (by linarith)
              have hw5 : (242372143/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_924 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (4307/4096:ℝ) with hc | hc
          · rcases le_total y (8069/4096:ℝ) with hc | hc
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
              have hw1 : (1679250671/2500000000000:ℝ) ≤ wfun y := wc_129 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
              have hw5 : (242372143/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_924 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
              have hw1 : (3220913463/5000000000000:ℝ) ≤ wfun y := wc_135 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_353 (x + y) (by linarith) (by linarith)
              have hw4 : (41/1250000000000:ℝ) ≤ wfun (y + z) := wc_354 (y + z) (by linarith) (by linarith)
              have hw5 : (1265836939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_947 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
            have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_130 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
            have hw3 : (41/1250000000000:ℝ) ≤ wfun (x + y) := wc_354 (x + y) (by linarith) (by linarith)
            have hw5 : (1264316833/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_948 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total z (2151/2048:ℝ) with hc | hc
        · rcases le_total x (4307/4096:ℝ) with hc | hc
          · rcases le_total y (8079/4096:ℝ) with hc | hc
            · rcases le_total z (4297/4096:ℝ) with hc | hc
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
                have hw1 : (6172561523/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_359 (x + y) (by linarith) (by linarith)
                have hw5 : (1213318631/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_923 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
                have hw1 : (6172561523/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_359 (x + y) (by linarith) (by linarith)
                have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_353 (y + z) (by linarith) (by linarith)
                have hw5 : (1267359331/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_946 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (4297/4096:ℝ) with hc | hc
              · rcases le_total x (8609/8192:ℝ) with hc | hc
                · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                  have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_139 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                  have hw3 : (4662827/10000000000000:ℝ) ≤ wfun (x + y) := wc_373 (x + y) (by linarith) (by linarith)
                  have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_353 (y + z) (by linarith) (by linarith)
                  have hw5 : (634060693/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_945 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                  have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_139 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                  have hw3 : (7258139/10000000000000:ℝ) ≤ wfun (x + y) := wc_380 (x + y) (by linarith) (by linarith)
                  have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_353 (y + z) (by linarith) (by linarith)
                  have hw5 : (647786457/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_955 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
                have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_139 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_374 (x + y) (by linarith) (by linarith)
                have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_359 (y + z) (by linarith) (by linarith)
                have hw5 : (52900211/400000000000:ℝ) ≤ wfun (x + y + z) := wc_966 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (8079/4096:ℝ) with hc | hc
            · rcases le_total z (4297/4096:ℝ) with hc | hc
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
                have hw1 : (6172561523/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_374 (x + y) (by linarith) (by linarith)
                have hw5 : (1267359331/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_946 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
                have hw1 : (6172561523/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_374 (x + y) (by linarith) (by linarith)
                have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_353 (y + z) (by linarith) (by linarith)
                have hw5 : (52900211/400000000000:ℝ) ≤ wfun (x + y + z) := wc_966 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (4297/4096:ℝ) with hc | hc
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
                have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_139 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_387 (x + y) (by linarith) (by linarith)
                have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_353 (y + z) (by linarith) (by linarith)
                have hw5 : (52900211/400000000000:ℝ) ≤ wfun (x + y + z) := wc_966 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
                have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_139 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_387 (x + y) (by linarith) (by linarith)
                have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_359 (y + z) (by linarith) (by linarith)
                have hw5 : (275750223/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_990 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (4307/4096:ℝ) with hc | hc
          · rcases le_total y (8079/4096:ℝ) with hc | hc
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
              have hw1 : (6172561523/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
              have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_359 (x + y) (by linarith) (by linarith)
              have hw4 : (29587/250000000000:ℝ) ≤ wfun (y + z) := wc_360 (y + z) (by linarith) (by linarith)
              have hw5 : (660458559/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_967 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (4307/4096:ℝ) with hc | hc
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
                have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_139 y (by linarith) (by linarith)
                have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
                have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_374 (x + y) (by linarith) (by linarith)
                have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_374 (y + z) (by linarith) (by linarith)
                have hw5 : (275750223/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_990 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
                have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_139 y (by linarith) (by linarith)
                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
                have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_374 (x + y) (by linarith) (by linarith)
                have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_387 (y + z) (by linarith) (by linarith)
                have hw5 : (718045723/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1011 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (8079/4096:ℝ) with hc | hc
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
              have hw1 : (6172561523/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
              have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_374 (x + y) (by linarith) (by linarith)
              have hw4 : (29587/250000000000:ℝ) ≤ wfun (y + z) := wc_360 (y + z) (by linarith) (by linarith)
              have hw5 : (172136989/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_991 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
              have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_139 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
              have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_387 (x + y) (by linarith) (by linarith)
              have hw4 : (465149/1000000000000:ℝ) ≤ wfun (y + z) := wc_375 (y + z) (by linarith) (by linarith)
              have hw5 : (57374717/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1012 (x + y + z) (by linarith) (by linarith)
              linarith

set_option maxHeartbeats 20000000 in
lemma ch_89 (x y z : ℝ) (hx1 : (4287/4096:ℝ) ≤ x) (hx2 : x ≤ (1073/1024:ℝ))
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
    · rcases le_total x (8579/8192:ℝ) with hc | hc
      · rcases le_total y (16213/8192:ℝ) with hc | hc
        · rcases le_total z (8549/8192:ℝ) with hc | hc
          · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
            have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
            have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
            have hw4 : (1187329/10000000000000:ℝ) ≤ wfun (y + z) := wc_357 (y + z) (by linarith) (by linarith)
            have hw5 : (116248451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_906 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
            have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
            have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
            have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
            have hw5 : (47554307/400000000000:ℝ) ≤ wfun (x + y + z) := wc_914 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (8549/8192:ℝ) with hc | hc
          · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
            have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
            have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_409 (x + y) (by linarith) (by linarith)
            have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
            have hw5 : (47554307/400000000000:ℝ) ≤ wfun (x + y + z) := wc_914 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (2920523/1250000000000:ℝ) ≤ wfun (x + y) := wc_408 (x + y) (by linarith) (by linarith)
              have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
              have hw5 : (1215875267/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_919 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (26016381/10000000000000:ℝ) ≤ wfun (x + y) := wc_412 (x + y) (by linarith) (by linarith)
              have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
              have hw5 : (307327397/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_933 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total y (16213/8192:ℝ) with hc | hc
        · rcases le_total z (8549/8192:ℝ) with hc | hc
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
            have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
            have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_409 (x + y) (by linarith) (by linarith)
            have hw4 : (1187329/10000000000000:ℝ) ≤ wfun (y + z) := wc_357 (y + z) (by linarith) (by linarith)
            have hw5 : (47554307/400000000000:ℝ) ≤ wfun (x + y + z) := wc_914 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
            have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
            have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_409 (x + y) (by linarith) (by linarith)
            have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
            have hw5 : (1215509621/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_920 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (8549/8192:ℝ) with hc | hc
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
            have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
            have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
            have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
            have hw5 : (1215509621/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_920 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (3601311/1250000000000:ℝ) ≤ wfun (x + y) := wc_414 (x + y) (by linarith) (by linarith)
              have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
              have hw5 : (621406689/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_935 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (6349281/2000000000000:ℝ) ≤ wfun (x + y) := wc_424 (x + y) (by linarith) (by linarith)
              have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
              have hw5 : (628193277/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_940 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total x (8579/8192:ℝ) with hc | hc
      · rcases le_total y (16213/8192:ℝ) with hc | hc
        · rcases le_total z (8559/8192:ℝ) with hc | hc
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (18485909/10000000000000:ℝ) ≤ wfun (x + y) := wc_400 (x + y) (by linarith) (by linarith)
              have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
              have hw5 : (1215875267/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_919 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (10426997/5000000000000:ℝ) ≤ wfun (x + y) := wc_406 (x + y) (by linarith) (by linarith)
              have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
              have hw5 : (307327397/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_933 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · rcases le_total y (32421/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
                have hw4 : (7266981/10000000000000:ℝ) ≤ wfun (y + z) := wc_378 (y + z) (by linarith) (by linarith)
                have hw5 : (1243187209/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_934 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
                have hw4 : (4390211/5000000000000:ℝ) ≤ wfun (y + z) := wc_382 (y + z) (by linarith) (by linarith)
                have hw5 : (1256764439/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_939 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32421/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
                have hw4 : (7266981/10000000000000:ℝ) ≤ wfun (y + z) := wc_378 (y + z) (by linarith) (by linarith)
                have hw5 : (1256764439/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_939 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
                have hw4 : (4390211/5000000000000:ℝ) ≤ wfun (y + z) := wc_382 (y + z) (by linarith) (by linarith)
                have hw5 : (1270410991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_941 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (8559/8192:ℝ) with hc | hc
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (2920523/1250000000000:ℝ) ≤ wfun (x + y) := wc_408 (x + y) (by linarith) (by linarith)
              have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
              have hw5 : (621406689/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_935 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total y (32431/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
                have hw4 : (7266981/10000000000000:ℝ) ≤ wfun (y + z) := wc_378 (y + z) (by linarith) (by linarith)
                have hw5 : (1256764439/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_939 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
                have hw4 : (4390211/5000000000000:ℝ) ≤ wfun (y + z) := wc_382 (y + z) (by linarith) (by linarith)
                have hw5 : (1270410991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_941 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · rcases le_total y (32431/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
                have hw4 : (5218271/5000000000000:ℝ) ≤ wfun (y + z) := wc_384 (y + z) (by linarith) (by linarith)
                have hw5 : (1270410991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_941 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
                have hw4 : (2447049/2000000000000:ℝ) ≤ wfun (y + z) := wc_392 (y + z) (by linarith) (by linarith)
                have hw5 : (1284126783/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_949 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32431/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
                have hw4 : (5218271/5000000000000:ℝ) ≤ wfun (y + z) := wc_384 (y + z) (by linarith) (by linarith)
                have hw5 : (1284126783/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_949 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
                have hw4 : (2447049/2000000000000:ℝ) ≤ wfun (y + z) := wc_392 (y + z) (by linarith) (by linarith)
                have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total y (16213/8192:ℝ) with hc | hc
        · rcases le_total z (8559/8192:ℝ) with hc | hc
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (2920523/1250000000000:ℝ) ≤ wfun (x + y) := wc_408 (x + y) (by linarith) (by linarith)
              have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
              have hw5 : (621406689/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_935 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (26016381/10000000000000:ℝ) ≤ wfun (x + y) := wc_412 (x + y) (by linarith) (by linarith)
              have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
              have hw5 : (628193277/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_940 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · rcases le_total y (32421/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
                have hw4 : (7266981/10000000000000:ℝ) ≤ wfun (y + z) := wc_378 (y + z) (by linarith) (by linarith)
                have hw5 : (1270410991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_941 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
                have hw4 : (4390211/5000000000000:ℝ) ≤ wfun (y + z) := wc_382 (y + z) (by linarith) (by linarith)
                have hw5 : (1284126783/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_949 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32421/16384:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
                have hw4 : (7266981/10000000000000:ℝ) ≤ wfun (y + z) := wc_378 (y + z) (by linarith) (by linarith)
                have hw5 : (1284126783/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_949 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
                have hw4 : (4390211/5000000000000:ℝ) ≤ wfun (y + z) := wc_382 (y + z) (by linarith) (by linarith)
                have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (8559/8192:ℝ) with hc | hc
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · rcases le_total y (32431/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
                have hw4 : (7266981/10000000000000:ℝ) ≤ wfun (y + z) := wc_378 (y + z) (by linarith) (by linarith)
                have hw5 : (1270410991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_941 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
                have hw4 : (4390211/5000000000000:ℝ) ≤ wfun (y + z) := wc_382 (y + z) (by linarith) (by linarith)
                have hw5 : (1284126783/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_949 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32431/16384:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
                have hw4 : (7266981/10000000000000:ℝ) ≤ wfun (y + z) := wc_378 (y + z) (by linarith) (by linarith)
                have hw5 : (1284126783/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_949 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
                have hw4 : (4390211/5000000000000:ℝ) ≤ wfun (y + z) := wc_382 (y + z) (by linarith) (by linarith)
                have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · rcases le_total y (32431/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
                have hw4 : (5218271/5000000000000:ℝ) ≤ wfun (y + z) := wc_384 (y + z) (by linarith) (by linarith)
                have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
                have hw4 : (2447049/2000000000000:ℝ) ≤ wfun (y + z) := wc_392 (y + z) (by linarith) (by linarith)
                have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32431/16384:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
                have hw4 : (5218271/5000000000000:ℝ) ≤ wfun (y + z) := wc_384 (y + z) (by linarith) (by linarith)
                have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
                have hw4 : (2447049/2000000000000:ℝ) ≤ wfun (y + z) := wc_392 (y + z) (by linarith) (by linarith)
                have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
                linarith
  · rcases le_total z (4277/4096:ℝ) with hc | hc
    · rcases le_total x (8579/8192:ℝ) with hc | hc
      · rcases le_total y (16223/8192:ℝ) with hc | hc
        · rcases le_total z (8549/8192:ℝ) with hc | hc
          · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
            have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
            have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
            have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
            have hw5 : (1215509621/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_920 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (3601311/1250000000000:ℝ) ≤ wfun (x + y) := wc_414 (x + y) (by linarith) (by linarith)
              have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
              have hw5 : (621406689/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_935 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (6349281/2000000000000:ℝ) ≤ wfun (x + y) := wc_424 (x + y) (by linarith) (by linarith)
              have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
              have hw5 : (628193277/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_940 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (8549/8192:ℝ) with hc | hc
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (8706009/2500000000000:ℝ) ≤ wfun (x + y) := wc_426 (x + y) (by linarith) (by linarith)
              have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
              have hw5 : (621406689/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_935 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (38043279/10000000000000:ℝ) ≤ wfun (x + y) := wc_430 (x + y) (by linarith) (by linarith)
              have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
              have hw5 : (628193277/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_940 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (8706009/2500000000000:ℝ) ≤ wfun (x + y) := wc_426 (x + y) (by linarith) (by linarith)
              have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
              have hw5 : (158753629/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_942 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (38043279/10000000000000:ℝ) ≤ wfun (x + y) := wc_430 (x + y) (by linarith) (by linarith)
              have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
              have hw5 : (1283740729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_950 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total y (16223/8192:ℝ) with hc | hc
        · rcases le_total z (8549/8192:ℝ) with hc | hc
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
            have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
            have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_427 (x + y) (by linarith) (by linarith)
            have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
            have hw5 : (155304961/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_936 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (8706009/2500000000000:ℝ) ≤ wfun (x + y) := wc_426 (x + y) (by linarith) (by linarith)
              have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
              have hw5 : (158753629/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_942 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (38043279/10000000000000:ℝ) ≤ wfun (x + y) := wc_430 (x + y) (by linarith) (by linarith)
              have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
              have hw5 : (1283740729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_950 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (8549/8192:ℝ) with hc | hc
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (10351009/2500000000000:ℝ) ≤ wfun (x + y) := wc_432 (x + y) (by linarith) (by linarith)
              have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
              have hw5 : (158753629/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_942 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (22453103/5000000000000:ℝ) ≤ wfun (x + y) := wc_438 (x + y) (by linarith) (by linarith)
              have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
              have hw5 : (1283740729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_950 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (10351009/2500000000000:ℝ) ≤ wfun (x + y) := wc_432 (x + y) (by linarith) (by linarith)
              have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
              have hw5 : (648760781/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_952 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (22453103/5000000000000:ℝ) ≤ wfun (x + y) := wc_438 (x + y) (by linarith) (by linarith)
              have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
              have hw5 : (1311371447/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_959 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total x (8579/8192:ℝ) with hc | hc
      · rcases le_total y (16223/8192:ℝ) with hc | hc
        · rcases le_total z (8559/8192:ℝ) with hc | hc
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · rcases le_total y (32441/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
                have hw4 : (5218271/5000000000000:ℝ) ≤ wfun (y + z) := wc_384 (y + z) (by linarith) (by linarith)
                have hw5 : (1270410991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_941 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
                have hw4 : (2447049/2000000000000:ℝ) ≤ wfun (y + z) := wc_392 (y + z) (by linarith) (by linarith)
                have hw5 : (1284126783/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_949 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32441/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
                have hw4 : (5218271/5000000000000:ℝ) ≤ wfun (y + z) := wc_384 (y + z) (by linarith) (by linarith)
                have hw5 : (1284126783/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_949 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
                have hw4 : (2447049/2000000000000:ℝ) ≤ wfun (y + z) := wc_392 (y + z) (by linarith) (by linarith)
                have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · rcases le_total y (32441/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
                have hw4 : (7088219/5000000000000:ℝ) ≤ wfun (y + z) := wc_394 (y + z) (by linarith) (by linarith)
                have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
                have hw4 : (650401/400000000000:ℝ) ≤ wfun (y + z) := wc_398 (y + z) (by linarith) (by linarith)
                have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32441/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
                have hw4 : (7088219/5000000000000:ℝ) ≤ wfun (y + z) := wc_394 (y + z) (by linarith) (by linarith)
                have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
                have hw4 : (650401/400000000000:ℝ) ≤ wfun (y + z) := wc_398 (y + z) (by linarith) (by linarith)
                have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (8559/8192:ℝ) with hc | hc
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · rcases le_total y (32451/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
                have hw4 : (7088219/5000000000000:ℝ) ≤ wfun (y + z) := wc_394 (y + z) (by linarith) (by linarith)
                have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
                have hw4 : (650401/400000000000:ℝ) ≤ wfun (y + z) := wc_398 (y + z) (by linarith) (by linarith)
                have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32451/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
                have hw4 : (7088219/5000000000000:ℝ) ≤ wfun (y + z) := wc_394 (y + z) (by linarith) (by linarith)
                have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
                have hw4 : (650401/400000000000:ℝ) ≤ wfun (y + z) := wc_398 (y + z) (by linarith) (by linarith)
                have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · rcases le_total y (32451/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
                have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
                have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
                have hw4 : (10426997/5000000000000:ℝ) ≤ wfun (y + z) := wc_406 (y + z) (by linarith) (by linarith)
                have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32451/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
                have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
                have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
                have hw4 : (10426997/5000000000000:ℝ) ≤ wfun (y + z) := wc_406 (y + z) (by linarith) (by linarith)
                have hw5 : (676870703/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_976 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total y (16223/8192:ℝ) with hc | hc
        · rcases le_total z (8559/8192:ℝ) with hc | hc
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · rcases le_total y (32441/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
                have hw4 : (5218271/5000000000000:ℝ) ≤ wfun (y + z) := wc_384 (y + z) (by linarith) (by linarith)
                have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
                have hw4 : (2447049/2000000000000:ℝ) ≤ wfun (y + z) := wc_392 (y + z) (by linarith) (by linarith)
                have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32441/16384:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
                have hw4 : (5218271/5000000000000:ℝ) ≤ wfun (y + z) := wc_384 (y + z) (by linarith) (by linarith)
                have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
                have hw4 : (2447049/2000000000000:ℝ) ≤ wfun (y + z) := wc_392 (y + z) (by linarith) (by linarith)
                have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · rcases le_total y (32441/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
                have hw4 : (7088219/5000000000000:ℝ) ≤ wfun (y + z) := wc_394 (y + z) (by linarith) (by linarith)
                have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
                have hw4 : (650401/400000000000:ℝ) ≤ wfun (y + z) := wc_398 (y + z) (by linarith) (by linarith)
                have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32441/16384:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
                have hw4 : (7088219/5000000000000:ℝ) ≤ wfun (y + z) := wc_394 (y + z) (by linarith) (by linarith)
                have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
                have hw4 : (650401/400000000000:ℝ) ≤ wfun (y + z) := wc_398 (y + z) (by linarith) (by linarith)
                have hw5 : (676870703/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_976 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (8559/8192:ℝ) with hc | hc
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · rcases le_total y (32451/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
                have hw4 : (7088219/5000000000000:ℝ) ≤ wfun (y + z) := wc_394 (y + z) (by linarith) (by linarith)
                have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
                have hw4 : (650401/400000000000:ℝ) ≤ wfun (y + z) := wc_398 (y + z) (by linarith) (by linarith)
                have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32451/16384:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
                have hw4 : (7088219/5000000000000:ℝ) ≤ wfun (y + z) := wc_394 (y + z) (by linarith) (by linarith)
                have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
                have hw4 : (650401/400000000000:ℝ) ≤ wfun (y + z) := wc_398 (y + z) (by linarith) (by linarith)
                have hw5 : (676870703/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_976 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · rcases le_total y (32451/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
                have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
                have hw5 : (676870703/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_976 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
                have hw4 : (10426997/5000000000000:ℝ) ≤ wfun (y + z) := wc_406 (y + z) (by linarith) (by linarith)
                have hw5 : (170983859/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_982 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32451/16384:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
                have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
                have hw5 : (170983859/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_982 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
                have hw4 : (10426997/5000000000000:ℝ) ≤ wfun (y + z) := wc_406 (y + z) (by linarith) (by linarith)
                have hw5 : (1382068991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_985 (x + y + z) (by linarith) (by linarith)
                linarith

set_option maxHeartbeats 20000000 in
lemma ch_91 (x y z : ℝ) (hx1 : (2141/2048:ℝ) ≤ x) (hx2 : x ≤ (4287/4096:ℝ))
    (hy1 : (8109/4096:ℝ) ≤ y) (hy2 : y ≤ (4057/2048:ℝ))
    (hz1 : (2141/2048:ℝ) ≤ z) (hz2 : z ≤ (4287/4096:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (8569/8192:ℝ) with hc | hc
  · rcases le_total y (16223/8192:ℝ) with hc | hc
    · rcases le_total z (8569/8192:ℝ) with hc | hc
      · rcases le_total x (17133/16384:ℝ) with hc | hc
        · rcases le_total y (32441/16384:ℝ) with hc | hc
          · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
            have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
            have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
            have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
            have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
            have hw5 : (1270410991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_941 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
            have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
            have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
            have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
            have hw4 : (10426997/5000000000000:ℝ) ≤ wfun (y + z) := wc_406 (y + z) (by linarith) (by linarith)
            have hw5 : (1284126783/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_949 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (32441/16384:ℝ) with hc | hc
          · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
            have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
            have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
            have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
            have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
            have hw5 : (1284126783/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_949 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
            have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
            have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
            have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
            have hw4 : (10426997/5000000000000:ℝ) ≤ wfun (y + z) := wc_406 (y + z) (by linarith) (by linarith)
            have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total x (17133/16384:ℝ) with hc | hc
        · rcases le_total y (32441/16384:ℝ) with hc | hc
          · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
            have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
            have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
            have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
            have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
            have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
            have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
            have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
            have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
            have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
            have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (32441/16384:ℝ) with hc | hc
          · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
            have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
            have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
            have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
            have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
            have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total z (17143/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
              have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
              have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
              have hw4 : (13013467/5000000000000:ℝ) ≤ wfun (y + z) := wc_411 (y + z) (by linarith) (by linarith)
              have hw5 : (1326087369/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_960 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
              have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
              have hw4 : (28822173/10000000000000:ℝ) ≤ wfun (y + z) := wc_413 (y + z) (by linarith) (by linarith)
              have hw5 : (1340083459/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_972 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total z (8569/8192:ℝ) with hc | hc
      · rcases le_total x (17133/16384:ℝ) with hc | hc
        · rcases le_total y (32451/16384:ℝ) with hc | hc
          · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
            have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
            have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
            have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
            have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
            have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
            have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
            have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
            have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
            have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
            have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (32451/16384:ℝ) with hc | hc
          · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
            have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
            have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
            have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
            have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
            have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total z (17133/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
              have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
              have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
              have hw4 : (13013467/5000000000000:ℝ) ≤ wfun (y + z) := wc_411 (y + z) (by linarith) (by linarith)
              have hw5 : (1326087369/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_960 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
              have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
              have hw4 : (28822173/10000000000000:ℝ) ≤ wfun (y + z) := wc_413 (y + z) (by linarith) (by linarith)
              have hw5 : (1340083459/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_972 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (17133/16384:ℝ) with hc | hc
        · rcases le_total y (32451/16384:ℝ) with hc | hc
          · rcases le_total z (17143/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
              have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
              have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
              have hw4 : (28822173/10000000000000:ℝ) ≤ wfun (y + z) := wc_413 (y + z) (by linarith) (by linarith)
              have hw5 : (1326087369/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_960 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
              have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
              have hw4 : (396991/125000000000:ℝ) ≤ wfun (y + z) := wc_423 (y + z) (by linarith) (by linarith)
              have hw5 : (1340083459/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_972 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17143/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
              have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
              have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
              have hw4 : (396991/125000000000:ℝ) ≤ wfun (y + z) := wc_423 (y + z) (by linarith) (by linarith)
              have hw5 : (1340083459/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_972 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
              have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
              have hw4 : (8709539/2500000000000:ℝ) ≤ wfun (y + z) := wc_425 (y + z) (by linarith) (by linarith)
              have hw5 : (338537097/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_975 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (32451/16384:ℝ) with hc | hc
          · rcases le_total z (17143/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
              have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
              have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
              have hw4 : (28822173/10000000000000:ℝ) ≤ wfun (y + z) := wc_413 (y + z) (by linarith) (by linarith)
              have hw5 : (1340083459/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_972 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
              have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
              have hw4 : (396991/125000000000:ℝ) ≤ wfun (y + z) := wc_423 (y + z) (by linarith) (by linarith)
              have hw5 : (338537097/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_975 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17143/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
              have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
              have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
              have hw4 : (396991/125000000000:ℝ) ≤ wfun (y + z) := wc_423 (y + z) (by linarith) (by linarith)
              have hw5 : (338537097/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_975 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
              have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
              have hw4 : (8709539/2500000000000:ℝ) ≤ wfun (y + z) := wc_425 (y + z) (by linarith) (by linarith)
              have hw5 : (171035259/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_981 (x + y + z) (by linarith) (by linarith)
              linarith
  · rcases le_total y (16223/8192:ℝ) with hc | hc
    · rcases le_total z (8569/8192:ℝ) with hc | hc
      · rcases le_total x (17143/16384:ℝ) with hc | hc
        · rcases le_total y (32441/16384:ℝ) with hc | hc
          · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
            have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
            have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
            have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
            have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
            have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total z (17133/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
              have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
              have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
              have hw4 : (4172491/2000000000000:ℝ) ≤ wfun (y + z) := wc_405 (y + z) (by linarith) (by linarith)
              have hw5 : (328040051/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_957 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
              have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
              have hw4 : (11686831/5000000000000:ℝ) ≤ wfun (y + z) := wc_407 (y + z) (by linarith) (by linarith)
              have hw5 : (1326087369/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_960 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (32441/16384:ℝ) with hc | hc
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
            have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
            have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
            have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
            have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
            have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total z (17133/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
              have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
              have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
              have hw4 : (4172491/2000000000000:ℝ) ≤ wfun (y + z) := wc_405 (y + z) (by linarith) (by linarith)
              have hw5 : (1326087369/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_960 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
              have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
              have hw4 : (11686831/5000000000000:ℝ) ≤ wfun (y + z) := wc_407 (y + z) (by linarith) (by linarith)
              have hw5 : (1340083459/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_972 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (17143/16384:ℝ) with hc | hc
        · rcases le_total y (32441/16384:ℝ) with hc | hc
          · rcases le_total z (17143/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
              have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
              have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
              have hw4 : (11686831/5000000000000:ℝ) ≤ wfun (y + z) := wc_407 (y + z) (by linarith) (by linarith)
              have hw5 : (1326087369/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_960 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
              have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
              have hw4 : (13013467/5000000000000:ℝ) ≤ wfun (y + z) := wc_411 (y + z) (by linarith) (by linarith)
              have hw5 : (1340083459/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_972 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17143/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
              have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
              have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
              have hw4 : (13013467/5000000000000:ℝ) ≤ wfun (y + z) := wc_411 (y + z) (by linarith) (by linarith)
              have hw5 : (1340083459/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_972 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
              have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
              have hw4 : (28822173/10000000000000:ℝ) ≤ wfun (y + z) := wc_413 (y + z) (by linarith) (by linarith)
              have hw5 : (338537097/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_975 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (32441/16384:ℝ) with hc | hc
          · rcases le_total z (17143/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
              have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
              have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
              have hw4 : (11686831/5000000000000:ℝ) ≤ wfun (y + z) := wc_407 (y + z) (by linarith) (by linarith)
              have hw5 : (1340083459/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_972 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
              have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
              have hw4 : (13013467/5000000000000:ℝ) ≤ wfun (y + z) := wc_411 (y + z) (by linarith) (by linarith)
              have hw5 : (338537097/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_975 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17143/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
              have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
              have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
              have hw4 : (13013467/5000000000000:ℝ) ≤ wfun (y + z) := wc_411 (y + z) (by linarith) (by linarith)
              have hw5 : (338537097/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_975 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
              have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
              have hw4 : (28822173/10000000000000:ℝ) ≤ wfun (y + z) := wc_413 (y + z) (by linarith) (by linarith)
              have hw5 : (171035259/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_981 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total z (8569/8192:ℝ) with hc | hc
      · rcases le_total x (17143/16384:ℝ) with hc | hc
        · rcases le_total y (32451/16384:ℝ) with hc | hc
          · rcases le_total z (17133/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
              have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
              have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
              have hw4 : (11686831/5000000000000:ℝ) ≤ wfun (y + z) := wc_407 (y + z) (by linarith) (by linarith)
              have hw5 : (1326087369/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_960 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
              have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
              have hw4 : (13013467/5000000000000:ℝ) ≤ wfun (y + z) := wc_411 (y + z) (by linarith) (by linarith)
              have hw5 : (1340083459/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_972 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17133/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
              have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
              have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
              have hw4 : (13013467/5000000000000:ℝ) ≤ wfun (y + z) := wc_411 (y + z) (by linarith) (by linarith)
              have hw5 : (1340083459/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_972 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
              have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
              have hw4 : (28822173/10000000000000:ℝ) ≤ wfun (y + z) := wc_413 (y + z) (by linarith) (by linarith)
              have hw5 : (338537097/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_975 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (32451/16384:ℝ) with hc | hc
          · rcases le_total z (17133/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
              have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
              have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
              have hw4 : (11686831/5000000000000:ℝ) ≤ wfun (y + z) := wc_407 (y + z) (by linarith) (by linarith)
              have hw5 : (1340083459/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_972 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
              have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
              have hw4 : (13013467/5000000000000:ℝ) ≤ wfun (y + z) := wc_411 (y + z) (by linarith) (by linarith)
              have hw5 : (338537097/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_975 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17133/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
              have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
              have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
              have hw4 : (13013467/5000000000000:ℝ) ≤ wfun (y + z) := wc_411 (y + z) (by linarith) (by linarith)
              have hw5 : (338537097/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_975 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
              have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
              have hw4 : (28822173/10000000000000:ℝ) ≤ wfun (y + z) := wc_413 (y + z) (by linarith) (by linarith)
              have hw5 : (171035259/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_981 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (17143/16384:ℝ) with hc | hc
        · rcases le_total y (32451/16384:ℝ) with hc | hc
          · rcases le_total z (17143/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
              have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
              have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
              have hw4 : (28822173/10000000000000:ℝ) ≤ wfun (y + z) := wc_413 (y + z) (by linarith) (by linarith)
              have hw5 : (338537097/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_975 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
              have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
              have hw4 : (396991/125000000000:ℝ) ≤ wfun (y + z) := wc_423 (y + z) (by linarith) (by linarith)
              have hw5 : (171035259/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_981 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17143/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
              have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
              have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
              have hw4 : (396991/125000000000:ℝ) ≤ wfun (y + z) := wc_423 (y + z) (by linarith) (by linarith)
              have hw5 : (171035259/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_981 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
              have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
              have hw4 : (8709539/2500000000000:ℝ) ≤ wfun (y + z) := wc_425 (y + z) (by linarith) (by linarith)
              have hw5 : (1382484427/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_984 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (32451/16384:ℝ) with hc | hc
          · rcases le_total z (17143/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
              have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
              have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
              have hw4 : (28822173/10000000000000:ℝ) ≤ wfun (y + z) := wc_413 (y + z) (by linarith) (by linarith)
              have hw5 : (171035259/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_981 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
              have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
              have hw4 : (396991/125000000000:ℝ) ≤ wfun (y + z) := wc_423 (y + z) (by linarith) (by linarith)
              have hw5 : (1382484427/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_984 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17143/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
              have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
              have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
              have hw4 : (396991/125000000000:ℝ) ≤ wfun (y + z) := wc_423 (y + z) (by linarith) (by linarith)
              have hw5 : (1382484427/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_984 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
              have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
              have hw4 : (8709539/2500000000000:ℝ) ≤ wfun (y + z) := wc_425 (y + z) (by linarith) (by linarith)
              have hw5 : (174594421/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_993 (x + y + z) (by linarith) (by linarith)
              linarith

set_option maxHeartbeats 20000000 in
lemma ch_104 (x y z : ℝ) (hx1 : (4287/4096:ℝ) ≤ x) (hx2 : x ≤ (1073/1024:ℝ))
    (hy1 : (4057/2048:ℝ) ≤ y) (hy2 : y ≤ (8119/4096:ℝ))
    (hz1 : (2141/2048:ℝ) ≤ z) (hz2 : z ≤ (4287/4096:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (8579/8192:ℝ) with hc | hc
  · rcases le_total y (16233/8192:ℝ) with hc | hc
    · rcases le_total z (8569/8192:ℝ) with hc | hc
      · rcases le_total x (17153/16384:ℝ) with hc | hc
        · rcases le_total y (32461/16384:ℝ) with hc | hc
          · rcases le_total z (17133/16384:ℝ) with hc | hc
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
              have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
              have hw4 : (28822173/10000000000000:ℝ) ≤ wfun (y + z) := wc_413 (y + z) (by linarith) (by linarith)
              have hw5 : (1382484427/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_984 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
              have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
              have hw4 : (396991/125000000000:ℝ) ≤ wfun (y + z) := wc_423 (y + z) (by linarith) (by linarith)
              have hw5 : (174594421/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_993 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17133/16384:ℝ) with hc | hc
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
              have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
              have hw4 : (396991/125000000000:ℝ) ≤ wfun (y + z) := wc_423 (y + z) (by linarith) (by linarith)
              have hw5 : (174594421/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_993 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
              have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
              have hw4 : (8709539/2500000000000:ℝ) ≤ wfun (y + z) := wc_425 (y + z) (by linarith) (by linarith)
              have hw5 : (1411094809/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_996 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (32461/16384:ℝ) with hc | hc
          · rcases le_total z (17133/16384:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
              have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
              have hw4 : (28822173/10000000000000:ℝ) ≤ wfun (y + z) := wc_413 (y + z) (by linarith) (by linarith)
              have hw5 : (174594421/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_993 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
              have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
              have hw4 : (396991/125000000000:ℝ) ≤ wfun (y + z) := wc_423 (y + z) (by linarith) (by linarith)
              have hw5 : (1411094809/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_996 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17133/16384:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
              have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
              have hw4 : (396991/125000000000:ℝ) ≤ wfun (y + z) := wc_423 (y + z) (by linarith) (by linarith)
              have hw5 : (1411094809/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_996 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
              have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
              have hw4 : (8709539/2500000000000:ℝ) ≤ wfun (y + z) := wc_425 (y + z) (by linarith) (by linarith)
              have hw5 : (285100533/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1002 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (17153/16384:ℝ) with hc | hc
        · rcases le_total y (32461/16384:ℝ) with hc | hc
          · rcases le_total z (17143/16384:ℝ) with hc | hc
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
              have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
              have hw4 : (8709539/2500000000000:ℝ) ≤ wfun (y + z) := wc_425 (y + z) (by linarith) (by linarith)
              have hw5 : (1411094809/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_996 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
              have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
              have hw4 : (2378669/625000000000:ℝ) ≤ wfun (y + z) := wc_429 (y + z) (by linarith) (by linarith)
              have hw5 : (285100533/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1002 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17143/16384:ℝ) with hc | hc
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
              have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
              have hw4 : (2378669/625000000000:ℝ) ≤ wfun (y + z) := wc_429 (y + z) (by linarith) (by linarith)
              have hw5 : (285100533/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1002 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
              have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
              have hw4 : (41420821/10000000000000:ℝ) ≤ wfun (y + z) := wc_431 (y + z) (by linarith) (by linarith)
              have hw5 : (1439978849/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1005 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (32461/16384:ℝ) with hc | hc
          · rcases le_total z (17143/16384:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
              have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
              have hw4 : (8709539/2500000000000:ℝ) ≤ wfun (y + z) := wc_425 (y + z) (by linarith) (by linarith)
              have hw5 : (285100533/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1002 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
              have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
              have hw4 : (2378669/625000000000:ℝ) ≤ wfun (y + z) := wc_429 (y + z) (by linarith) (by linarith)
              have hw5 : (1439978849/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1005 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17143/16384:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
              have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
              have hw4 : (2378669/625000000000:ℝ) ≤ wfun (y + z) := wc_429 (y + z) (by linarith) (by linarith)
              have hw5 : (1439978849/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1005 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
              have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
              have hw4 : (41420821/10000000000000:ℝ) ≤ wfun (y + z) := wc_431 (y + z) (by linarith) (by linarith)
              have hw5 : (363630819/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1026 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total z (8569/8192:ℝ) with hc | hc
      · rcases le_total x (17153/16384:ℝ) with hc | hc
        · rcases le_total y (32471/16384:ℝ) with hc | hc
          · rcases le_total z (17133/16384:ℝ) with hc | hc
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
              have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
              have hw4 : (8709539/2500000000000:ℝ) ≤ wfun (y + z) := wc_425 (y + z) (by linarith) (by linarith)
              have hw5 : (1411094809/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_996 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
              have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
              have hw4 : (2378669/625000000000:ℝ) ≤ wfun (y + z) := wc_429 (y + z) (by linarith) (by linarith)
              have hw5 : (285100533/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1002 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17133/16384:ℝ) with hc | hc
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
              have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
              have hw4 : (2378669/625000000000:ℝ) ≤ wfun (y + z) := wc_429 (y + z) (by linarith) (by linarith)
              have hw5 : (285100533/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1002 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
              have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
              have hw4 : (41420821/10000000000000:ℝ) ≤ wfun (y + z) := wc_431 (y + z) (by linarith) (by linarith)
              have hw5 : (1439978849/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1005 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (32471/16384:ℝ) with hc | hc
          · rcases le_total z (17133/16384:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
              have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
              have hw4 : (8709539/2500000000000:ℝ) ≤ wfun (y + z) := wc_425 (y + z) (by linarith) (by linarith)
              have hw5 : (285100533/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1002 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
              have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
              have hw4 : (2378669/625000000000:ℝ) ≤ wfun (y + z) := wc_429 (y + z) (by linarith) (by linarith)
              have hw5 : (1439978849/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1005 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17133/16384:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
              have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
              have hw4 : (2378669/625000000000:ℝ) ≤ wfun (y + z) := wc_429 (y + z) (by linarith) (by linarith)
              have hw5 : (1439978849/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1005 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
              have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
              have hw4 : (41420821/10000000000000:ℝ) ≤ wfun (y + z) := wc_431 (y + z) (by linarith) (by linarith)
              have hw5 : (363630819/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1026 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (17153/16384:ℝ) with hc | hc
        · rcases le_total y (32471/16384:ℝ) with hc | hc
          · rcases le_total z (17143/16384:ℝ) with hc | hc
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
              have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
              have hw4 : (41420821/10000000000000:ℝ) ≤ wfun (y + z) := wc_431 (y + z) (by linarith) (by linarith)
              have hw5 : (1439978849/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1005 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
              have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
              have hw4 : (4492441/1000000000000:ℝ) ≤ wfun (y + z) := wc_437 (y + z) (by linarith) (by linarith)
              have hw5 : (363630819/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1026 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17143/16384:ℝ) with hc | hc
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
              have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
              have hw4 : (4492441/1000000000000:ℝ) ≤ wfun (y + z) := wc_437 (y + z) (by linarith) (by linarith)
              have hw5 : (363630819/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1026 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
              have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
              have hw4 : (6071171/1250000000000:ℝ) ≤ wfun (y + z) := wc_439 (y + z) (by linarith) (by linarith)
              have hw5 : (73456793/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1029 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (32471/16384:ℝ) with hc | hc
          · rcases le_total z (17143/16384:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
              have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
              have hw4 : (41420821/10000000000000:ℝ) ≤ wfun (y + z) := wc_431 (y + z) (by linarith) (by linarith)
              have hw5 : (363630819/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1026 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
              have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
              have hw4 : (4492441/1000000000000:ℝ) ≤ wfun (y + z) := wc_437 (y + z) (by linarith) (by linarith)
              have hw5 : (73456793/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1029 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17143/16384:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
              have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
              have hw4 : (4492441/1000000000000:ℝ) ≤ wfun (y + z) := wc_437 (y + z) (by linarith) (by linarith)
              have hw5 : (73456793/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1029 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
              have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
              have hw4 : (6071171/1250000000000:ℝ) ≤ wfun (y + z) := wc_439 (y + z) (by linarith) (by linarith)
              have hw5 : (296763303/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1035 (x + y + z) (by linarith) (by linarith)
              linarith
  · rcases le_total y (16233/8192:ℝ) with hc | hc
    · rcases le_total z (8569/8192:ℝ) with hc | hc
      · rcases le_total x (17163/16384:ℝ) with hc | hc
        · rcases le_total y (32461/16384:ℝ) with hc | hc
          · rcases le_total z (17133/16384:ℝ) with hc | hc
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
              have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
              have hw4 : (28822173/10000000000000:ℝ) ≤ wfun (y + z) := wc_413 (y + z) (by linarith) (by linarith)
              have hw5 : (1411094809/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_996 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
              have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
              have hw4 : (396991/125000000000:ℝ) ≤ wfun (y + z) := wc_423 (y + z) (by linarith) (by linarith)
              have hw5 : (285100533/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1002 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17133/16384:ℝ) with hc | hc
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
              have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
              have hw4 : (396991/125000000000:ℝ) ≤ wfun (y + z) := wc_423 (y + z) (by linarith) (by linarith)
              have hw5 : (285100533/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1002 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
              have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
              have hw4 : (8709539/2500000000000:ℝ) ≤ wfun (y + z) := wc_425 (y + z) (by linarith) (by linarith)
              have hw5 : (1439978849/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1005 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (32461/16384:ℝ) with hc | hc
          · rcases le_total z (17133/16384:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
              have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
              have hw4 : (28822173/10000000000000:ℝ) ≤ wfun (y + z) := wc_413 (y + z) (by linarith) (by linarith)
              have hw5 : (285100533/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1002 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
              have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
              have hw4 : (396991/125000000000:ℝ) ≤ wfun (y + z) := wc_423 (y + z) (by linarith) (by linarith)
              have hw5 : (1439978849/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1005 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17133/16384:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
              have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
              have hw4 : (396991/125000000000:ℝ) ≤ wfun (y + z) := wc_423 (y + z) (by linarith) (by linarith)
              have hw5 : (1439978849/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1005 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
              have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
              have hw4 : (8709539/2500000000000:ℝ) ≤ wfun (y + z) := wc_425 (y + z) (by linarith) (by linarith)
              have hw5 : (363630819/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1026 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (17163/16384:ℝ) with hc | hc
        · rcases le_total y (32461/16384:ℝ) with hc | hc
          · rcases le_total z (17143/16384:ℝ) with hc | hc
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
              have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
              have hw4 : (8709539/2500000000000:ℝ) ≤ wfun (y + z) := wc_425 (y + z) (by linarith) (by linarith)
              have hw5 : (1439978849/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1005 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
              have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
              have hw4 : (2378669/625000000000:ℝ) ≤ wfun (y + z) := wc_429 (y + z) (by linarith) (by linarith)
              have hw5 : (363630819/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1026 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17143/16384:ℝ) with hc | hc
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
              have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
              have hw4 : (2378669/625000000000:ℝ) ≤ wfun (y + z) := wc_429 (y + z) (by linarith) (by linarith)
              have hw5 : (363630819/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1026 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
              have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
              have hw4 : (41420821/10000000000000:ℝ) ≤ wfun (y + z) := wc_431 (y + z) (by linarith) (by linarith)
              have hw5 : (73456793/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1029 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (32461/16384:ℝ) with hc | hc
          · rcases le_total z (17143/16384:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
              have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
              have hw4 : (8709539/2500000000000:ℝ) ≤ wfun (y + z) := wc_425 (y + z) (by linarith) (by linarith)
              have hw5 : (363630819/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1026 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
              have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
              have hw4 : (2378669/625000000000:ℝ) ≤ wfun (y + z) := wc_429 (y + z) (by linarith) (by linarith)
              have hw5 : (73456793/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1029 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17143/16384:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
              have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
              have hw4 : (2378669/625000000000:ℝ) ≤ wfun (y + z) := wc_429 (y + z) (by linarith) (by linarith)
              have hw5 : (73456793/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1029 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
              have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
              have hw4 : (41420821/10000000000000:ℝ) ≤ wfun (y + z) := wc_431 (y + z) (by linarith) (by linarith)
              have hw5 : (296763303/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1035 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total z (8569/8192:ℝ) with hc | hc
      · rcases le_total x (17163/16384:ℝ) with hc | hc
        · rcases le_total y (32471/16384:ℝ) with hc | hc
          · rcases le_total z (17133/16384:ℝ) with hc | hc
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
              have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
              have hw4 : (8709539/2500000000000:ℝ) ≤ wfun (y + z) := wc_425 (y + z) (by linarith) (by linarith)
              have hw5 : (1439978849/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1005 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
              have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
              have hw4 : (2378669/625000000000:ℝ) ≤ wfun (y + z) := wc_429 (y + z) (by linarith) (by linarith)
              have hw5 : (363630819/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1026 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17133/16384:ℝ) with hc | hc
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
              have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
              have hw4 : (2378669/625000000000:ℝ) ≤ wfun (y + z) := wc_429 (y + z) (by linarith) (by linarith)
              have hw5 : (363630819/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1026 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
              have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
              have hw4 : (41420821/10000000000000:ℝ) ≤ wfun (y + z) := wc_431 (y + z) (by linarith) (by linarith)
              have hw5 : (73456793/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1029 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (32471/16384:ℝ) with hc | hc
          · rcases le_total z (17133/16384:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
              have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
              have hw4 : (8709539/2500000000000:ℝ) ≤ wfun (y + z) := wc_425 (y + z) (by linarith) (by linarith)
              have hw5 : (363630819/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1026 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
              have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
              have hw4 : (2378669/625000000000:ℝ) ≤ wfun (y + z) := wc_429 (y + z) (by linarith) (by linarith)
              have hw5 : (73456793/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1029 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17133/16384:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
              have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
              have hw4 : (2378669/625000000000:ℝ) ≤ wfun (y + z) := wc_429 (y + z) (by linarith) (by linarith)
              have hw5 : (73456793/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1029 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
              have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
              have hw4 : (41420821/10000000000000:ℝ) ≤ wfun (y + z) := wc_431 (y + z) (by linarith) (by linarith)
              have hw5 : (296763303/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1035 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (17163/16384:ℝ) with hc | hc
        · rcases le_total y (32471/16384:ℝ) with hc | hc
          · rcases le_total z (17143/16384:ℝ) with hc | hc
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
              have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
              have hw4 : (41420821/10000000000000:ℝ) ≤ wfun (y + z) := wc_431 (y + z) (by linarith) (by linarith)
              have hw5 : (73456793/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1029 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
              have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
              have hw4 : (4492441/1000000000000:ℝ) ≤ wfun (y + z) := wc_437 (y + z) (by linarith) (by linarith)
              have hw5 : (296763303/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1035 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17143/16384:ℝ) with hc | hc
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
              have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
              have hw4 : (4492441/1000000000000:ℝ) ≤ wfun (y + z) := wc_437 (y + z) (by linarith) (by linarith)
              have hw5 : (296763303/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1035 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
              have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
              have hw4 : (6071171/1250000000000:ℝ) ≤ wfun (y + z) := wc_439 (y + z) (by linarith) (by linarith)
              have hw5 : (1498565153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1038 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (32471/16384:ℝ) with hc | hc
          · rcases le_total z (17143/16384:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
              have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
              have hw4 : (41420821/10000000000000:ℝ) ≤ wfun (y + z) := wc_431 (y + z) (by linarith) (by linarith)
              have hw5 : (296763303/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1035 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
              have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
              have hw4 : (4492441/1000000000000:ℝ) ≤ wfun (y + z) := wc_437 (y + z) (by linarith) (by linarith)
              have hw5 : (1498565153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1038 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17143/16384:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
              have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
              have hw4 : (4492441/1000000000000:ℝ) ≤ wfun (y + z) := wc_437 (y + z) (by linarith) (by linarith)
              have hw5 : (1498565153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1038 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
              have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
              have hw4 : (6071171/1250000000000:ℝ) ≤ wfun (y + z) := wc_439 (y + z) (by linarith) (by linarith)
              have hw5 : (189172711/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1047 (x + y + z) (by linarith) (by linarith)
              linarith

set_option maxHeartbeats 20000000 in
lemma ch_147 (x y z : ℝ) (hx1 : (4297/4096:ℝ) ≤ x) (hx2 : x ≤ (2151/2048:ℝ))
    (hy1 : (4057/2048:ℝ) ≤ y) (hy2 : y ≤ (2031/1024:ℝ))
    (hz1 : (2141/2048:ℝ) ≤ z) (hz2 : z ≤ (1073/1024:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total y (8119/4096:ℝ) with hc | hc
  · rcases le_total z (4287/4096:ℝ) with hc | hc
    · rcases le_total x (8599/8192:ℝ) with hc | hc
      · rcases le_total y (16233/8192:ℝ) with hc | hc
        · rcases le_total z (8569/8192:ℝ) with hc | hc
          · rcases le_total x (17193/16384:ℝ) with hc | hc
            · rcases le_total y (32461/16384:ℝ) with hc | hc
              · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
                have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
                have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
                have hw5 : (749057553/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1039 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
                have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
                have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
                have hw5 : (60517089/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1048 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32461/16384:ℝ) with hc | hc
              · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_80 x (by linarith) (by linarith)
                have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
                have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
                have hw5 : (60517089/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1048 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_80 x (by linarith) (by linarith)
                have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (82806113/10000000000000:ℝ) ≤ wfun (x + y) := wc_469 (x + y) (by linarith) (by linarith)
                have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
                have hw5 : (305561427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1051 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17193/16384:ℝ) with hc | hc
            · rcases le_total y (32461/16384:ℝ) with hc | hc
              · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
                have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
                have hw4 : (8706009/2500000000000:ℝ) ≤ wfun (y + z) := wc_426 (y + z) (by linarith) (by linarith)
                have hw5 : (305561427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1051 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
                have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
                have hw4 : (38043279/10000000000000:ℝ) ≤ wfun (y + z) := wc_430 (y + z) (by linarith) (by linarith)
                have hw5 : (1542754747/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1057 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32461/16384:ℝ) with hc | hc
              · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_80 x (by linarith) (by linarith)
                have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
                have hw4 : (8706009/2500000000000:ℝ) ≤ wfun (y + z) := wc_426 (y + z) (by linarith) (by linarith)
                have hw5 : (1542754747/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1057 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_80 x (by linarith) (by linarith)
                have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (82806113/10000000000000:ℝ) ≤ wfun (x + y) := wc_469 (x + y) (by linarith) (by linarith)
                have hw4 : (38043279/10000000000000:ℝ) ≤ wfun (y + z) := wc_430 (y + z) (by linarith) (by linarith)
                have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (8569/8192:ℝ) with hc | hc
          · rcases le_total x (17193/16384:ℝ) with hc | hc
            · rcases le_total y (32471/16384:ℝ) with hc | hc
              · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
                have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (82806113/10000000000000:ℝ) ≤ wfun (x + y) := wc_469 (x + y) (by linarith) (by linarith)
                have hw4 : (8706009/2500000000000:ℝ) ≤ wfun (y + z) := wc_426 (y + z) (by linarith) (by linarith)
                have hw5 : (305561427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1051 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
                have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (87718793/10000000000000:ℝ) ≤ wfun (x + y) := wc_473 (x + y) (by linarith) (by linarith)
                have hw4 : (38043279/10000000000000:ℝ) ≤ wfun (y + z) := wc_430 (y + z) (by linarith) (by linarith)
                have hw5 : (1542754747/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1057 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_80 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (17536657/2000000000000:ℝ) ≤ wfun (x + y) := wc_474 (x + y) (by linarith) (by linarith)
              have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
              have hw5 : (96393223/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1058 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17193/16384:ℝ) with hc | hc
            · rcases le_total y (32471/16384:ℝ) with hc | hc
              · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
                have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (82806113/10000000000000:ℝ) ≤ wfun (x + y) := wc_469 (x + y) (by linarith) (by linarith)
                have hw4 : (10351009/2500000000000:ℝ) ≤ wfun (y + z) := wc_432 (y + z) (by linarith) (by linarith)
                have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
                have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (87718793/10000000000000:ℝ) ≤ wfun (x + y) := wc_473 (x + y) (by linarith) (by linarith)
                have hw4 : (22453103/5000000000000:ℝ) ≤ wfun (y + z) := wc_438 (y + z) (by linarith) (by linarith)
                have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32471/16384:ℝ) with hc | hc
              · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_80 x (by linarith) (by linarith)
                have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (87718793/10000000000000:ℝ) ≤ wfun (x + y) := wc_473 (x + y) (by linarith) (by linarith)
                have hw4 : (10351009/2500000000000:ℝ) ≤ wfun (y + z) := wc_432 (y + z) (by linarith) (by linarith)
                have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_80 x (by linarith) (by linarith)
                have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (92771811/10000000000000:ℝ) ≤ wfun (x + y) := wc_475 (x + y) (by linarith) (by linarith)
                have hw4 : (22453103/5000000000000:ℝ) ≤ wfun (y + z) := wc_438 (y + z) (by linarith) (by linarith)
                have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total y (16233/8192:ℝ) with hc | hc
        · rcases le_total z (8569/8192:ℝ) with hc | hc
          · rcases le_total x (17203/16384:ℝ) with hc | hc
            · have hw0 : (207931583/5000000000000:ℝ) ≤ wfun x := wc_81 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (8277259/1000000000000:ℝ) ≤ wfun (x + y) := wc_470 (x + y) (by linarith) (by linarith)
              have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
              have hw5 : (1527348409/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1052 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_83 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (17536657/2000000000000:ℝ) ≤ wfun (x + y) := wc_474 (x + y) (by linarith) (by linarith)
              have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
              have hw5 : (96393223/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1058 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17203/16384:ℝ) with hc | hc
            · have hw0 : (207931583/5000000000000:ℝ) ≤ wfun x := wc_81 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (8277259/1000000000000:ℝ) ≤ wfun (x + y) := wc_470 (x + y) (by linarith) (by linarith)
              have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
              have hw5 : (778651161/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1061 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_83 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (17536657/2000000000000:ℝ) ≤ wfun (x + y) := wc_474 (x + y) (by linarith) (by linarith)
              have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
              have hw5 : (314476117/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1073 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (8569/8192:ℝ) with hc | hc
          · rcases le_total x (17203/16384:ℝ) with hc | hc
            · have hw0 : (207931583/5000000000000:ℝ) ≤ wfun x := wc_81 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (92734261/10000000000000:ℝ) ≤ wfun (x + y) := wc_476 (x + y) (by linarith) (by linarith)
              have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
              have hw5 : (778651161/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1061 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_83 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (97925413/10000000000000:ℝ) ≤ wfun (x + y) := wc_495 (x + y) (by linarith) (by linarith)
              have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
              have hw5 : (314476117/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1073 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17203/16384:ℝ) with hc | hc
            · have hw0 : (207931583/5000000000000:ℝ) ≤ wfun x := wc_81 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (92734261/10000000000000:ℝ) ≤ wfun (x + y) := wc_476 (x + y) (by linarith) (by linarith)
              have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
              have hw5 : (396881567/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1075 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_83 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (97925413/10000000000000:ℝ) ≤ wfun (x + y) := wc_495 (x + y) (by linarith) (by linarith)
              have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
              have hw5 : (1602739283/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1080 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total x (8599/8192:ℝ) with hc | hc
      · rcases le_total y (16233/8192:ℝ) with hc | hc
        · rcases le_total z (8579/8192:ℝ) with hc | hc
          · rcases le_total x (17193/16384:ℝ) with hc | hc
            · rcases le_total y (32461/16384:ℝ) with hc | hc
              · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
                have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
                have hw4 : (10351009/2500000000000:ℝ) ≤ wfun (y + z) := wc_432 (y + z) (by linarith) (by linarith)
                have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
                have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
                have hw4 : (22453103/5000000000000:ℝ) ≤ wfun (y + z) := wc_438 (y + z) (by linarith) (by linarith)
                have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32461/16384:ℝ) with hc | hc
              · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_80 x (by linarith) (by linarith)
                have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
                have hw4 : (10351009/2500000000000:ℝ) ≤ wfun (y + z) := wc_432 (y + z) (by linarith) (by linarith)
                have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_80 x (by linarith) (by linarith)
                have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (82806113/10000000000000:ℝ) ≤ wfun (x + y) := wc_469 (x + y) (by linarith) (by linarith)
                have hw4 : (22453103/5000000000000:ℝ) ≤ wfun (y + z) := wc_438 (y + z) (by linarith) (by linarith)
                have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17193/16384:ℝ) with hc | hc
            · rcases le_total y (32461/16384:ℝ) with hc | hc
              · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
                have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
                have hw4 : (48549689/10000000000000:ℝ) ≤ wfun (y + z) := wc_440 (y + z) (by linarith) (by linarith)
                have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
                have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
                have hw4 : (3270899/625000000000:ℝ) ≤ wfun (y + z) := wc_444 (y + z) (by linarith) (by linarith)
                have hw5 : (1603220471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1079 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_80 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (39001141/5000000000000:ℝ) ≤ wfun (x + y) := wc_468 (x + y) (by linarith) (by linarith)
              have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
              have hw5 : (1602739283/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1080 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (8579/8192:ℝ) with hc | hc
          · rcases le_total x (17193/16384:ℝ) with hc | hc
            · rcases le_total y (32471/16384:ℝ) with hc | hc
              · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
                have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (82806113/10000000000000:ℝ) ≤ wfun (x + y) := wc_469 (x + y) (by linarith) (by linarith)
                have hw4 : (48549689/10000000000000:ℝ) ≤ wfun (y + z) := wc_440 (y + z) (by linarith) (by linarith)
                have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
                have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (87718793/10000000000000:ℝ) ≤ wfun (x + y) := wc_473 (x + y) (by linarith) (by linarith)
                have hw4 : (3270899/625000000000:ℝ) ≤ wfun (y + z) := wc_444 (y + z) (by linarith) (by linarith)
                have hw5 : (1603220471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1079 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_80 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (17536657/2000000000000:ℝ) ≤ wfun (x + y) := wc_474 (x + y) (by linarith) (by linarith)
              have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
              have hw5 : (1602739283/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1080 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17193/16384:ℝ) with hc | hc
            · rcases le_total y (32471/16384:ℝ) with hc | hc
              · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
                have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (82806113/10000000000000:ℝ) ≤ wfun (x + y) := wc_469 (x + y) (by linarith) (by linarith)
                have hw4 : (56260189/10000000000000:ℝ) ≤ wfun (y + z) := wc_446 (y + z) (by linarith) (by linarith)
                have hw5 : (1618505281/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1081 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
                have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (87718793/10000000000000:ℝ) ≤ wfun (x + y) := wc_473 (x + y) (by linarith) (by linarith)
                have hw4 : (30163501/5000000000000:ℝ) ≤ wfun (y + z) := wc_454 (y + z) (by linarith) (by linarith)
                have hw5 : (816928633/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1089 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_80 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (17536657/2000000000000:ℝ) ≤ wfun (x + y) := wc_474 (x + y) (by linarith) (by linarith)
              have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
              have hw5 : (1633366957/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1090 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total y (16233/8192:ℝ) with hc | hc
        · rcases le_total z (8579/8192:ℝ) with hc | hc
          · rcases le_total x (17203/16384:ℝ) with hc | hc
            · have hw0 : (207931583/5000000000000:ℝ) ≤ wfun x := wc_81 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (8277259/1000000000000:ℝ) ≤ wfun (x + y) := wc_470 (x + y) (by linarith) (by linarith)
              have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
              have hw5 : (396881567/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1075 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_83 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (17536657/2000000000000:ℝ) ≤ wfun (x + y) := wc_474 (x + y) (by linarith) (by linarith)
              have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
              have hw5 : (1602739283/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1080 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17203/16384:ℝ) with hc | hc
            · have hw0 : (207931583/5000000000000:ℝ) ≤ wfun x := wc_81 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (8277259/1000000000000:ℝ) ≤ wfun (x + y) := wc_470 (x + y) (by linarith) (by linarith)
              have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
              have hw5 : (1618019543/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1082 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_83 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (17536657/2000000000000:ℝ) ≤ wfun (x + y) := wc_474 (x + y) (by linarith) (by linarith)
              have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
              have hw5 : (1633366957/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1090 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (8579/8192:ℝ) with hc | hc
          · rcases le_total x (17203/16384:ℝ) with hc | hc
            · have hw0 : (207931583/5000000000000:ℝ) ≤ wfun x := wc_81 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (92734261/10000000000000:ℝ) ≤ wfun (x + y) := wc_476 (x + y) (by linarith) (by linarith)
              have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
              have hw5 : (1618019543/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1082 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_83 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (97925413/10000000000000:ℝ) ≤ wfun (x + y) := wc_495 (x + y) (by linarith) (by linarith)
              have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
              have hw5 : (1633366957/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1090 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
            have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
            have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
            have hw5 : (65931469/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1093 (x + y + z) (by linarith) (by linarith)
            linarith
  · rcases le_total z (4287/4096:ℝ) with hc | hc
    · rcases le_total x (8599/8192:ℝ) with hc | hc
      · rcases le_total y (16243/8192:ℝ) with hc | hc
        · rcases le_total z (8569/8192:ℝ) with hc | hc
          · rcases le_total x (17193/16384:ℝ) with hc | hc
            · rcases le_total y (32481/16384:ℝ) with hc | hc
              · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (92771811/10000000000000:ℝ) ≤ wfun (x + y) := wc_475 (x + y) (by linarith) (by linarith)
                have hw4 : (10351009/2500000000000:ℝ) ≤ wfun (y + z) := wc_432 (y + z) (by linarith) (by linarith)
                have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (97965061/10000000000000:ℝ) ≤ wfun (x + y) := wc_494 (x + y) (by linarith) (by linarith)
                have hw4 : (22453103/5000000000000:ℝ) ≤ wfun (y + z) := wc_438 (y + z) (by linarith) (by linarith)
                have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_80 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (97925413/10000000000000:ℝ) ≤ wfun (x + y) := wc_495 (x + y) (by linarith) (by linarith)
              have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
              have hw5 : (314476117/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1073 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17193/16384:ℝ) with hc | hc
            · rcases le_total y (32481/16384:ℝ) with hc | hc
              · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (92771811/10000000000000:ℝ) ≤ wfun (x + y) := wc_475 (x + y) (by linarith) (by linarith)
                have hw4 : (48549689/10000000000000:ℝ) ≤ wfun (y + z) := wc_440 (y + z) (by linarith) (by linarith)
                have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (97965061/10000000000000:ℝ) ≤ wfun (x + y) := wc_494 (x + y) (by linarith) (by linarith)
                have hw4 : (3270899/625000000000:ℝ) ≤ wfun (y + z) := wc_444 (y + z) (by linarith) (by linarith)
                have hw5 : (1603220471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1079 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_80 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (97925413/10000000000000:ℝ) ≤ wfun (x + y) := wc_495 (x + y) (by linarith) (by linarith)
              have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
              have hw5 : (1602739283/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1080 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (8569/8192:ℝ) with hc | hc
          · rcases le_total x (17193/16384:ℝ) with hc | hc
            · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
              have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (20651327/2000000000000:ℝ) ≤ wfun (x + y) := wc_497 (x + y) (by linarith) (by linarith)
              have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
              have hw5 : (396881567/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1075 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_80 x (by linarith) (by linarith)
              have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (108727819/10000000000000:ℝ) ≤ wfun (x + y) := wc_501 (x + y) (by linarith) (by linarith)
              have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
              have hw5 : (1602739283/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1080 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17193/16384:ℝ) with hc | hc
            · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
              have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (20651327/2000000000000:ℝ) ≤ wfun (x + y) := wc_497 (x + y) (by linarith) (by linarith)
              have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
              have hw5 : (1618019543/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1082 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_80 x (by linarith) (by linarith)
              have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (108727819/10000000000000:ℝ) ≤ wfun (x + y) := wc_501 (x + y) (by linarith) (by linarith)
              have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
              have hw5 : (1633366957/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1090 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total y (16243/8192:ℝ) with hc | hc
        · rcases le_total z (8569/8192:ℝ) with hc | hc
          · rcases le_total x (17203/16384:ℝ) with hc | hc
            · have hw0 : (207931583/5000000000000:ℝ) ≤ wfun x := wc_81 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (20651327/2000000000000:ℝ) ≤ wfun (x + y) := wc_497 (x + y) (by linarith) (by linarith)
              have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
              have hw5 : (396881567/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1075 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_83 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (108727819/10000000000000:ℝ) ≤ wfun (x + y) := wc_501 (x + y) (by linarith) (by linarith)
              have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
              have hw5 : (1602739283/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1080 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17203/16384:ℝ) with hc | hc
            · have hw0 : (207931583/5000000000000:ℝ) ≤ wfun x := wc_81 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (20651327/2000000000000:ℝ) ≤ wfun (x + y) := wc_497 (x + y) (by linarith) (by linarith)
              have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
              have hw5 : (1618019543/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1082 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_83 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (108727819/10000000000000:ℝ) ≤ wfun (x + y) := wc_501 (x + y) (by linarith) (by linarith)
              have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
              have hw5 : (1633366957/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1090 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (8569/8192:ℝ) with hc | hc
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
            have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
            have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
            have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
            have hw5 : (1617533987/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1083 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
            have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
            have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
            have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
            have hw5 : (65931469/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1093 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total x (8599/8192:ℝ) with hc | hc
      · rcases le_total y (16243/8192:ℝ) with hc | hc
        · rcases le_total z (8579/8192:ℝ) with hc | hc
          · rcases le_total x (17193/16384:ℝ) with hc | hc
            · rcases le_total y (32481/16384:ℝ) with hc | hc
              · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (92771811/10000000000000:ℝ) ≤ wfun (x + y) := wc_475 (x + y) (by linarith) (by linarith)
                have hw4 : (56260189/10000000000000:ℝ) ≤ wfun (y + z) := wc_446 (y + z) (by linarith) (by linarith)
                have hw5 : (1618505281/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1081 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (97965061/10000000000000:ℝ) ≤ wfun (x + y) := wc_494 (x + y) (by linarith) (by linarith)
                have hw4 : (30163501/5000000000000:ℝ) ≤ wfun (y + z) := wc_454 (y + z) (by linarith) (by linarith)
                have hw5 : (816928633/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1089 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_80 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (97925413/10000000000000:ℝ) ≤ wfun (x + y) := wc_495 (x + y) (by linarith) (by linarith)
              have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
              have hw5 : (1633366957/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1090 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17193/16384:ℝ) with hc | hc
            · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (92734261/10000000000000:ℝ) ≤ wfun (x + y) := wc_476 (x + y) (by linarith) (by linarith)
              have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
              have hw5 : (824390719/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1092 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_80 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (97925413/10000000000000:ℝ) ≤ wfun (x + y) := wc_495 (x + y) (by linarith) (by linarith)
              have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
              have hw5 : (1664262897/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1097 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (8579/8192:ℝ) with hc | hc
          · rcases le_total x (17193/16384:ℝ) with hc | hc
            · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
              have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (20651327/2000000000000:ℝ) ≤ wfun (x + y) := wc_497 (x + y) (by linarith) (by linarith)
              have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
              have hw5 : (824390719/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1092 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_80 x (by linarith) (by linarith)
              have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (108727819/10000000000000:ℝ) ≤ wfun (x + y) := wc_501 (x + y) (by linarith) (by linarith)
              have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
              have hw5 : (1664262897/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1097 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17193/16384:ℝ) with hc | hc
            · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
              have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (20651327/2000000000000:ℝ) ≤ wfun (x + y) := wc_497 (x + y) (by linarith) (by linarith)
              have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
              have hw5 : (1679811243/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1098 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_80 x (by linarith) (by linarith)
              have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (108727819/10000000000000:ℝ) ≤ wfun (x + y) := wc_501 (x + y) (by linarith) (by linarith)
              have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
              have hw5 : (1695426389/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1111 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total y (16243/8192:ℝ) with hc | hc
        · rcases le_total z (8579/8192:ℝ) with hc | hc
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
            have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
            have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
            have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
            have hw5 : (65931469/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1093 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
            have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
            have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
            have hw5 : (52478353/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1099 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (8579/8192:ℝ) with hc | hc
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
            have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
            have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
            have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
            have hw5 : (52478353/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1099 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
            have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
            have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
            have hw5 : (342118997/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1113 (x + y + z) (by linarith) (by linarith)
            linarith

set_option maxHeartbeats 20000000 in
lemma ch_161 (x y z : ℝ) (hx1 : (267/256:ℝ) ≤ x) (hx2 : x ≤ (539/512:ℝ))
    (hy1 : (1013/512:ℝ) ≤ y) (hy2 : y ≤ (509/256:ℝ))
    (hz1 : (539/512:ℝ) ≤ z) (hz2 : z ≤ (17/16:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (1073/1024:ℝ) with hc | hc
  · rcases le_total y (2031/1024:ℝ) with hc | hc
    · rcases le_total z (1083/1024:ℝ) with hc | hc
      · rcases le_total x (2141/2048:ℝ) with hc | hc
        · rcases le_total y (4057/2048:ℝ) with hc | hc
          · rcases le_total z (2161/2048:ℝ) with hc | hc
            · rcases le_total x (4277/4096:ℝ) with hc | hc
              · rcases le_total y (8109/4096:ℝ) with hc | hc
                · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                  have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_162 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_359 (x + y) (by linarith) (by linarith)
                  have hw4 : (5774823/625000000000:ℝ) ≤ wfun (y + z) := wc_480 (y + z) (by linarith) (by linarith)
                  have hw5 : (57374717/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1012 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                  have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_172 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_374 (x + y) (by linarith) (by linarith)
                  have hw4 : (569617/50000000000:ℝ) ≤ wfun (y + z) := wc_507 (y + z) (by linarith) (by linarith)
                  have hw5 : (1492727701/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1045 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (8109/4096:ℝ) with hc | hc
                · rcases le_total z (4317/4096:ℝ) with hc | hc
                  · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                    have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_162 y (by linarith) (by linarith)
                    have hw2 : (85656967/10000000000000:ℝ) ≤ wfun z := wc_92 z (by linarith) (by linarith)
                    have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_374 (x + y) (by linarith) (by linarith)
                    have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_479 (y + z) (by linarith) (by linarith)
                    have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1044 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                    have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_162 y (by linarith) (by linarith)
                    have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_95 z (by linarith) (by linarith)
                    have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_374 (x + y) (by linarith) (by linarith)
                    have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_506 (y + z) (by linarith) (by linarith)
                    have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1065 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total z (4317/4096:ℝ) with hc | hc
                  · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                    have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_172 y (by linarith) (by linarith)
                    have hw2 : (85656967/10000000000000:ℝ) ≤ wfun z := wc_92 z (by linarith) (by linarith)
                    have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_387 (x + y) (by linarith) (by linarith)
                    have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_506 (y + z) (by linarith) (by linarith)
                    have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1065 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                    have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_172 y (by linarith) (by linarith)
                    have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_95 z (by linarith) (by linarith)
                    have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_387 (x + y) (by linarith) (by linarith)
                    have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
                    have hw5 : (807312237/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1086 (x + y + z) (by linarith) (by linarith)
                    linarith
            · rcases le_total x (4277/4096:ℝ) with hc | hc
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_163 y (by linarith) (by linarith)
                have hw3 : (29587/250000000000:ℝ) ≤ wfun (x + y) := wc_360 (x + y) (by linarith) (by linarith)
                have hw4 : (13745521/1000000000000:ℝ) ≤ wfun (y + z) := wc_517 (y + z) (by linarith) (by linarith)
                have hw5 : (775154287/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1067 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_163 y (by linarith) (by linarith)
                have hw3 : (465149/1000000000000:ℝ) ≤ wfun (x + y) := wc_375 (x + y) (by linarith) (by linarith)
                have hw4 : (13745521/1000000000000:ℝ) ≤ wfun (y + z) := wc_517 (y + z) (by linarith) (by linarith)
                have hw5 : (1610755299/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1088 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (2161/2048:ℝ) with hc | hc
            · rcases le_total x (4277/4096:ℝ) with hc | hc
              · rcases le_total y (8119/4096:ℝ) with hc | hc
                · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                  have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_179 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_387 (x + y) (by linarith) (by linarith)
                  have hw4 : (4302423/312500000000:ℝ) ≤ wfun (y + z) := wc_516 (y + z) (by linarith) (by linarith)
                  have hw5 : (62086789/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1066 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                  have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_403 (x + y) (by linarith) (by linarith)
                  have hw4 : (163652657/10000000000000:ℝ) ≤ wfun (y + z) := wc_524 (y + z) (by linarith) (by linarith)
                  have hw5 : (322537687/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1087 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (8119/4096:ℝ) with hc | hc
                · rcases le_total z (4317/4096:ℝ) with hc | hc
                  · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                    have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_179 y (by linarith) (by linarith)
                    have hw2 : (85656967/10000000000000:ℝ) ≤ wfun z := wc_92 z (by linarith) (by linarith)
                    have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_403 (x + y) (by linarith) (by linarith)
                    have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
                    have hw5 : (807312237/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1086 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                    have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_179 y (by linarith) (by linarith)
                    have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_95 z (by linarith) (by linarith)
                    have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_403 (x + y) (by linarith) (by linarith)
                    have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
                    have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1102 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total z (4317/4096:ℝ) with hc | hc
                  · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                    have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
                    have hw2 : (85656967/10000000000000:ℝ) ≤ wfun z := wc_92 z (by linarith) (by linarith)
                    have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_417 (x + y) (by linarith) (by linarith)
                    have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
                    have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1102 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                    have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
                    have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_95 z (by linarith) (by linarith)
                    have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_417 (x + y) (by linarith) (by linarith)
                    have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_529 (y + z) (by linarith) (by linarith)
                    have hw5 : (1739017297/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1121 (x + y + z) (by linarith) (by linarith)
                    linarith
            · rcases le_total x (4277/4096:ℝ) with hc | hc
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_180 y (by linarith) (by linarith)
                have hw3 : (649907/625000000000:ℝ) ≤ wfun (x + y) := wc_388 (x + y) (by linarith) (by linarith)
                have hw4 : (23941523/1250000000000:ℝ) ≤ wfun (y + z) := wc_531 (y + z) (by linarith) (by linarith)
                have hw5 : (418067961/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1104 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_180 y (by linarith) (by linarith)
                have hw3 : (736743/400000000000:ℝ) ≤ wfun (x + y) := wc_404 (x + y) (by linarith) (by linarith)
                have hw4 : (23941523/1250000000000:ℝ) ≤ wfun (y + z) := wc_531 (y + z) (by linarith) (by linarith)
                have hw5 : (867426269/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1123 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total y (4057/2048:ℝ) with hc | hc
          · rcases le_total z (2161/2048:ℝ) with hc | hc
            · rcases le_total x (4287/4096:ℝ) with hc | hc
              · rcases le_total y (8109/4096:ℝ) with hc | hc
                · rcases le_total z (4317/4096:ℝ) with hc | hc
                  · rcases le_total x (8569/8192:ℝ) with hc | hc
                    · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                      have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_162 y (by linarith) (by linarith)
                      have hw2 : (85656967/10000000000000:ℝ) ≤ wfun z := wc_92 z (by linarith) (by linarith)
                      have hw3 : (5211923/5000000000000:ℝ) ≤ wfun (x + y) := wc_386 (x + y) (by linarith) (by linarith)
                      have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_479 (y + z) (by linarith) (by linarith)
                      have hw5 : (194370837/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1064 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
                      have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_162 y (by linarith) (by linarith)
                      have hw2 : (85656967/10000000000000:ℝ) ≤ wfun z := wc_92 z (by linarith) (by linarith)
                      have hw3 : (3539799/2500000000000:ℝ) ≤ wfun (x + y) := wc_396 (x + y) (by linarith) (by linarith)
                      have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_479 (y + z) (by linarith) (by linarith)
                      have hw5 : (1585145671/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1078 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
                    have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_162 y (by linarith) (by linarith)
                    have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_95 z (by linarith) (by linarith)
                    have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_387 (x + y) (by linarith) (by linarith)
                    have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_506 (y + z) (by linarith) (by linarith)
                    have hw5 : (807312237/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1086 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total z (4317/4096:ℝ) with hc | hc
                  · rcases le_total x (8569/8192:ℝ) with hc | hc
                    · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                      have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_172 y (by linarith) (by linarith)
                      have hw2 : (85656967/10000000000000:ℝ) ≤ wfun z := wc_92 z (by linarith) (by linarith)
                      have hw3 : (1846343/1000000000000:ℝ) ≤ wfun (x + y) := wc_402 (x + y) (by linarith) (by linarith)
                      have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_506 (y + z) (by linarith) (by linarith)
                      have hw5 : (100974599/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1085 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
                      have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_172 y (by linarith) (by linarith)
                      have hw2 : (85656967/10000000000000:ℝ) ≤ wfun z := wc_92 z (by linarith) (by linarith)
                      have hw3 : (23335779/10000000000000:ℝ) ≤ wfun (x + y) := wc_410 (x + y) (by linarith) (by linarith)
                      have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_506 (y + z) (by linarith) (by linarith)
                      have hw5 : (51447179/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1095 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
                    have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_172 y (by linarith) (by linarith)
                    have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_95 z (by linarith) (by linarith)
                    have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_403 (x + y) (by linarith) (by linarith)
                    have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
                    have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1102 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total y (8109/4096:ℝ) with hc | hc
                · rcases le_total z (4317/4096:ℝ) with hc | hc
                  · rcases le_total x (8579/8192:ℝ) with hc | hc
                    · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
                      have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_162 y (by linarith) (by linarith)
                      have hw2 : (85656967/10000000000000:ℝ) ≤ wfun z := wc_92 z (by linarith) (by linarith)
                      have hw3 : (1846343/1000000000000:ℝ) ≤ wfun (x + y) := wc_402 (x + y) (by linarith) (by linarith)
                      have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_479 (y + z) (by linarith) (by linarith)
                      have hw5 : (100974599/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1085 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
                      have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_162 y (by linarith) (by linarith)
                      have hw2 : (85656967/10000000000000:ℝ) ≤ wfun z := wc_92 z (by linarith) (by linarith)
                      have hw3 : (23335779/10000000000000:ℝ) ≤ wfun (x + y) := wc_410 (x + y) (by linarith) (by linarith)
                      have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_479 (y + z) (by linarith) (by linarith)
                      have hw5 : (51447179/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1095 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
                    have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_162 y (by linarith) (by linarith)
                    have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_95 z (by linarith) (by linarith)
                    have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_403 (x + y) (by linarith) (by linarith)
                    have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_506 (y + z) (by linarith) (by linarith)
                    have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1102 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total z (4317/4096:ℝ) with hc | hc
                  · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
                    have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_172 y (by linarith) (by linarith)
                    have hw2 : (85656967/10000000000000:ℝ) ≤ wfun z := wc_92 z (by linarith) (by linarith)
                    have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_417 (x + y) (by linarith) (by linarith)
                    have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_506 (y + z) (by linarith) (by linarith)
                    have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1102 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
                    have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_172 y (by linarith) (by linarith)
                    have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_95 z (by linarith) (by linarith)
                    have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_417 (x + y) (by linarith) (by linarith)
                    have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
                    have hw5 : (1739017297/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1121 (x + y + z) (by linarith) (by linarith)
                    linarith
            · rcases le_total x (4287/4096:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
                have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_163 y (by linarith) (by linarith)
                have hw3 : (649907/625000000000:ℝ) ≤ wfun (x + y) := wc_388 (x + y) (by linarith) (by linarith)
                have hw4 : (13745521/1000000000000:ℝ) ≤ wfun (y + z) := wc_517 (y + z) (by linarith) (by linarith)
                have hw5 : (418067961/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1104 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
                have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_163 y (by linarith) (by linarith)
                have hw3 : (736743/400000000000:ℝ) ≤ wfun (x + y) := wc_404 (x + y) (by linarith) (by linarith)
                have hw4 : (13745521/1000000000000:ℝ) ≤ wfun (y + z) := wc_517 (y + z) (by linarith) (by linarith)
                have hw5 : (867426269/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1123 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (2161/2048:ℝ) with hc | hc
            · rcases le_total x (4287/4096:ℝ) with hc | hc
              · rcases le_total y (8119/4096:ℝ) with hc | hc
                · rcases le_total z (4317/4096:ℝ) with hc | hc
                  · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
                    have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_179 y (by linarith) (by linarith)
                    have hw2 : (85656967/10000000000000:ℝ) ≤ wfun z := wc_92 z (by linarith) (by linarith)
                    have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_417 (x + y) (by linarith) (by linarith)
                    have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
                    have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1102 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
                    have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_179 y (by linarith) (by linarith)
                    have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_95 z (by linarith) (by linarith)
                    have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_417 (x + y) (by linarith) (by linarith)
                    have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
                    have hw5 : (1739017297/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1121 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total z (4317/4096:ℝ) with hc | hc
                  · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
                    have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
                    have hw2 : (85656967/10000000000000:ℝ) ≤ wfun z := wc_92 z (by linarith) (by linarith)
                    have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_435 (x + y) (by linarith) (by linarith)
                    have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
                    have hw5 : (1739017297/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1121 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
                    have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
                    have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_95 z (by linarith) (by linarith)
                    have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_435 (x + y) (by linarith) (by linarith)
                    have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_529 (y + z) (by linarith) (by linarith)
                    have hw5 : (112675493/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1130 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total y (8119/4096:ℝ) with hc | hc
                · rcases le_total z (4317/4096:ℝ) with hc | hc
                  · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
                    have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_179 y (by linarith) (by linarith)
                    have hw2 : (85656967/10000000000000:ℝ) ≤ wfun z := wc_92 z (by linarith) (by linarith)
                    have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_435 (x + y) (by linarith) (by linarith)
                    have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
                    have hw5 : (1739017297/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1121 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
                    have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_179 y (by linarith) (by linarith)
                    have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_95 z (by linarith) (by linarith)
                    have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_435 (x + y) (by linarith) (by linarith)
                    have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
                    have hw5 : (112675493/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1130 (x + y + z) (by linarith) (by linarith)
                    linarith
                · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
                  have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_449 (x + y) (by linarith) (by linarith)
                  have hw4 : (163652657/10000000000000:ℝ) ≤ wfun (y + z) := wc_524 (y + z) (by linarith) (by linarith)
                  have hw5 : (1800648153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1131 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total x (4287/4096:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
                have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_180 y (by linarith) (by linarith)
                have hw3 : (2870559/1000000000000:ℝ) ≤ wfun (x + y) := wc_418 (x + y) (by linarith) (by linarith)
                have hw4 : (23941523/1250000000000:ℝ) ≤ wfun (y + z) := wc_531 (y + z) (by linarith) (by linarith)
                have hw5 : (1798491653/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1132 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
                have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_180 y (by linarith) (by linarith)
                have hw3 : (20626673/5000000000000:ℝ) ≤ wfun (x + y) := wc_436 (x + y) (by linarith) (by linarith)
                have hw4 : (23941523/1250000000000:ℝ) ≤ wfun (y + z) := wc_531 (y + z) (by linarith) (by linarith)
                have hw5 : (1863183413/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1142 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total x (2141/2048:ℝ) with hc | hc
        · rcases le_total y (4057/2048:ℝ) with hc | hc
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
            have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_163 y (by linarith) (by linarith)
            have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_98 z (by linarith) (by linarith)
            have hw3 : (1181561/10000000000000:ℝ) ≤ wfun (x + y) := wc_361 (x + y) (by linarith) (by linarith)
            have hw4 : (7636599/400000000000:ℝ) ≤ wfun (y + z) := wc_532 (y + z) (by linarith) (by linarith)
            have hw5 : (1666270777/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1106 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
            have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_180 y (by linarith) (by linarith)
            have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_98 z (by linarith) (by linarith)
            have hw3 : (2076333/2000000000000:ℝ) ≤ wfun (x + y) := wc_389 (x + y) (by linarith) (by linarith)
            have hw4 : (63400731/2500000000000:ℝ) ≤ wfun (y + z) := wc_545 (y + z) (by linarith) (by linarith)
            have hw5 : (1792041507/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1134 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (4057/2048:ℝ) with hc | hc
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_56 x (by linarith) (by linarith)
            have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_163 y (by linarith) (by linarith)
            have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_98 z (by linarith) (by linarith)
            have hw3 : (2076333/2000000000000:ℝ) ≤ wfun (x + y) := wc_389 (x + y) (by linarith) (by linarith)
            have hw4 : (7636599/400000000000:ℝ) ≤ wfun (y + z) := wc_532 (y + z) (by linarith) (by linarith)
            have hw5 : (1792041507/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1134 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_56 x (by linarith) (by linarith)
            have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_180 y (by linarith) (by linarith)
            have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_98 z (by linarith) (by linarith)
            have hw3 : (14329561/5000000000000:ℝ) ≤ wfun (x + y) := wc_419 (x + y) (by linarith) (by linarith)
            have hw4 : (63400731/2500000000000:ℝ) ≤ wfun (y + z) := wc_545 (y + z) (by linarith) (by linarith)
            have hw5 : (1922008203/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1149 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total z (1083/1024:ℝ) with hc | hc
      · rcases le_total x (2141/2048:ℝ) with hc | hc
        · rcases le_total y (4067/2048:ℝ) with hc | hc
          · rcases le_total z (2161/2048:ℝ) with hc | hc
            · rcases le_total x (4277/4096:ℝ) with hc | hc
              · rcases le_total y (8129/4096:ℝ) with hc | hc
                · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                  have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_417 (x + y) (by linarith) (by linarith)
                  have hw4 : (47960431/2500000000000:ℝ) ≤ wfun (y + z) := wc_530 (y + z) (by linarith) (by linarith)
                  have hw5 : (334855641/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1103 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                  have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_435 (x + y) (by linarith) (by linarith)
                  have hw4 : (111118793/5000000000000:ℝ) ≤ wfun (y + z) := wc_540 (y + z) (by linarith) (by linarith)
                  have hw5 : (434233339/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1122 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (8129/4096:ℝ) with hc | hc
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                  have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_435 (x + y) (by linarith) (by linarith)
                  have hw4 : (47960431/2500000000000:ℝ) ≤ wfun (y + z) := wc_530 (y + z) (by linarith) (by linarith)
                  have hw5 : (434233339/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1122 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                  have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_449 (x + y) (by linarith) (by linarith)
                  have hw4 : (111118793/5000000000000:ℝ) ≤ wfun (y + z) := wc_540 (y + z) (by linarith) (by linarith)
                  have hw5 : (1800648153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1131 (x + y + z) (by linarith) (by linarith)
                  linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
              have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_195 y (by linarith) (by linarith)
              have hw3 : (14329561/5000000000000:ℝ) ≤ wfun (x + y) := wc_419 (x + y) (by linarith) (by linarith)
              have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_544 (y + z) (by linarith) (by linarith)
              have hw5 : (1796338383/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1133 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (2161/2048:ℝ) with hc | hc
            · rcases le_total x (4277/4096:ℝ) with hc | hc
              · rcases le_total y (8139/4096:ℝ) with hc | hc
                · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                  have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_449 (x + y) (by linarith) (by linarith)
                  have hw4 : (10193319/400000000000:ℝ) ≤ wfun (y + z) := wc_543 (y + z) (by linarith) (by linarith)
                  have hw5 : (1800648153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1131 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                  have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_465 (x + y) (by linarith) (by linarith)
                  have hw4 : (289620509/10000000000000:ℝ) ≤ wfun (y + z) := wc_549 (y + z) (by linarith) (by linarith)
                  have hw5 : (1865416811/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1141 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (8139/4096:ℝ) with hc | hc
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                  have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_465 (x + y) (by linarith) (by linarith)
                  have hw4 : (10193319/400000000000:ℝ) ≤ wfun (y + z) := wc_543 (y + z) (by linarith) (by linarith)
                  have hw5 : (1865416811/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1141 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                  have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_479 (x + y) (by linarith) (by linarith)
                  have hw4 : (289620509/10000000000000:ℝ) ≤ wfun (y + z) := wc_549 (y + z) (by linarith) (by linarith)
                  have hw5 : (965616743/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1146 (x + y + z) (by linarith) (by linarith)
                  linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
              have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_210 y (by linarith) (by linarith)
              have hw3 : (55964847/10000000000000:ℝ) ≤ wfun (x + y) := wc_451 (x + y) (by linarith) (by linarith)
              have hw4 : (326066581/10000000000000:ℝ) ≤ wfun (y + z) := wc_552 (y + z) (by linarith) (by linarith)
              have hw5 : (963306969/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1148 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (4067/2048:ℝ) with hc | hc
          · rcases le_total z (2161/2048:ℝ) with hc | hc
            · rcases le_total x (4287/4096:ℝ) with hc | hc
              · rcases le_total y (8129/4096:ℝ) with hc | hc
                · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
                  have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_449 (x + y) (by linarith) (by linarith)
                  have hw4 : (47960431/2500000000000:ℝ) ≤ wfun (y + z) := wc_530 (y + z) (by linarith) (by linarith)
                  have hw5 : (1800648153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1131 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
                  have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_465 (x + y) (by linarith) (by linarith)
                  have hw4 : (111118793/5000000000000:ℝ) ≤ wfun (y + z) := wc_540 (y + z) (by linarith) (by linarith)
                  have hw5 : (1865416811/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1141 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (8129/4096:ℝ) with hc | hc
                · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
                  have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_465 (x + y) (by linarith) (by linarith)
                  have hw4 : (47960431/2500000000000:ℝ) ≤ wfun (y + z) := wc_530 (y + z) (by linarith) (by linarith)
                  have hw5 : (1865416811/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1141 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
                  have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_479 (x + y) (by linarith) (by linarith)
                  have hw4 : (111118793/5000000000000:ℝ) ≤ wfun (y + z) := wc_540 (y + z) (by linarith) (by linarith)
                  have hw5 : (965616743/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1146 (x + y + z) (by linarith) (by linarith)
                  linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_56 x (by linarith) (by linarith)
              have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_195 y (by linarith) (by linarith)
              have hw3 : (55964847/10000000000000:ℝ) ≤ wfun (x + y) := wc_451 (x + y) (by linarith) (by linarith)
              have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_544 (y + z) (by linarith) (by linarith)
              have hw5 : (963306969/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1148 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (2161/2048:ℝ) with hc | hc
            · rcases le_total x (4287/4096:ℝ) with hc | hc
              · rcases le_total y (8139/4096:ℝ) with hc | hc
                · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
                  have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_479 (x + y) (by linarith) (by linarith)
                  have hw4 : (10193319/400000000000:ℝ) ≤ wfun (y + z) := wc_543 (y + z) (by linarith) (by linarith)
                  have hw5 : (965616743/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1146 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
                  have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_506 (x + y) (by linarith) (by linarith)
                  have hw4 : (289620509/10000000000000:ℝ) ≤ wfun (y + z) := wc_549 (y + z) (by linarith) (by linarith)
                  have hw5 : (49952307/250000000000:ℝ) ≤ wfun (x + y + z) := wc_1159 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
                have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_210 y (by linarith) (by linarith)
                have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                have hw3 : (569617/50000000000:ℝ) ≤ wfun (x + y) := wc_507 (x + y) (by linarith) (by linarith)
                have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_544 (y + z) (by linarith) (by linarith)
                have hw5 : (1995701471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1160 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_56 x (by linarith) (by linarith)
              have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_210 y (by linarith) (by linarith)
              have hw3 : (92247841/10000000000000:ℝ) ≤ wfun (x + y) := wc_481 (x + y) (by linarith) (by linarith)
              have hw4 : (326066581/10000000000000:ℝ) ≤ wfun (y + z) := wc_552 (y + z) (by linarith) (by linarith)
              have hw5 : (2061048329/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1164 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (2141/2048:ℝ) with hc | hc
        · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
          have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_196 y (by linarith) (by linarith)
          have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_98 z (by linarith) (by linarith)
          have hw3 : (7141617/2500000000000:ℝ) ≤ wfun (x + y) := wc_420 (x + y) (by linarith) (by linarith)
          have hw4 : (161986357/5000000000000:ℝ) ≤ wfun (y + z) := wc_554 (y + z) (by linarith) (by linarith)
          have hw5 : (1917416231/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1150 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_56 x (by linarith) (by linarith)
          have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_196 y (by linarith) (by linarith)
          have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_98 z (by linarith) (by linarith)
          have hw3 : (27892031/5000000000000:ℝ) ≤ wfun (x + y) := wc_452 (x + y) (by linarith) (by linarith)
          have hw4 : (161986357/5000000000000:ℝ) ≤ wfun (y + z) := wc_554 (y + z) (by linarith) (by linarith)
          have hw5 : (410242943/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1166 (x + y + z) (by linarith) (by linarith)
          linarith
  · rcases le_total y (2031/1024:ℝ) with hc | hc
    · rcases le_total z (1083/1024:ℝ) with hc | hc
      · rcases le_total x (2151/2048:ℝ) with hc | hc
        · rcases le_total y (4057/2048:ℝ) with hc | hc
          · rcases le_total z (2161/2048:ℝ) with hc | hc
            · rcases le_total x (4297/4096:ℝ) with hc | hc
              · rcases le_total y (8109/4096:ℝ) with hc | hc
                · rcases le_total z (4317/4096:ℝ) with hc | hc
                  · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                    have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_162 y (by linarith) (by linarith)
                    have hw2 : (85656967/10000000000000:ℝ) ≤ wfun z := wc_92 z (by linarith) (by linarith)
                    have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_417 (x + y) (by linarith) (by linarith)
                    have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_479 (y + z) (by linarith) (by linarith)
                    have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1102 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                    have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_162 y (by linarith) (by linarith)
                    have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_95 z (by linarith) (by linarith)
                    have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_417 (x + y) (by linarith) (by linarith)
                    have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_506 (y + z) (by linarith) (by linarith)
                    have hw5 : (1739017297/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1121 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total z (4317/4096:ℝ) with hc | hc
                  · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                    have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_172 y (by linarith) (by linarith)
                    have hw2 : (85656967/10000000000000:ℝ) ≤ wfun z := wc_92 z (by linarith) (by linarith)
                    have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_435 (x + y) (by linarith) (by linarith)
                    have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_506 (y + z) (by linarith) (by linarith)
                    have hw5 : (1739017297/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1121 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                    have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_172 y (by linarith) (by linarith)
                    have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_95 z (by linarith) (by linarith)
                    have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_435 (x + y) (by linarith) (by linarith)
                    have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
                    have hw5 : (112675493/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1130 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total y (8109/4096:ℝ) with hc | hc
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
                  have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_162 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_435 (x + y) (by linarith) (by linarith)
                  have hw4 : (5774823/625000000000:ℝ) ≤ wfun (y + z) := wc_480 (y + z) (by linarith) (by linarith)
                  have hw5 : (434233339/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1122 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
                  have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_172 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_449 (x + y) (by linarith) (by linarith)
                  have hw4 : (569617/50000000000:ℝ) ≤ wfun (y + z) := wc_507 (y + z) (by linarith) (by linarith)
                  have hw5 : (1800648153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1131 (x + y + z) (by linarith) (by linarith)
                  linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
              have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_163 y (by linarith) (by linarith)
              have hw3 : (14329561/5000000000000:ℝ) ≤ wfun (x + y) := wc_419 (x + y) (by linarith) (by linarith)
              have hw4 : (13745521/1000000000000:ℝ) ≤ wfun (y + z) := wc_517 (y + z) (by linarith) (by linarith)
              have hw5 : (1796338383/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1133 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (2161/2048:ℝ) with hc | hc
            · rcases le_total x (4297/4096:ℝ) with hc | hc
              · rcases le_total y (8119/4096:ℝ) with hc | hc
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                  have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_179 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_449 (x + y) (by linarith) (by linarith)
                  have hw4 : (4302423/312500000000:ℝ) ≤ wfun (y + z) := wc_516 (y + z) (by linarith) (by linarith)
                  have hw5 : (1800648153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1131 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                  have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_465 (x + y) (by linarith) (by linarith)
                  have hw4 : (163652657/10000000000000:ℝ) ≤ wfun (y + z) := wc_524 (y + z) (by linarith) (by linarith)
                  have hw5 : (1865416811/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1141 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (8119/4096:ℝ) with hc | hc
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
                  have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_179 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_465 (x + y) (by linarith) (by linarith)
                  have hw4 : (4302423/312500000000:ℝ) ≤ wfun (y + z) := wc_516 (y + z) (by linarith) (by linarith)
                  have hw5 : (1865416811/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1141 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
                  have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_479 (x + y) (by linarith) (by linarith)
                  have hw4 : (163652657/10000000000000:ℝ) ≤ wfun (y + z) := wc_524 (y + z) (by linarith) (by linarith)
                  have hw5 : (965616743/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1146 (x + y + z) (by linarith) (by linarith)
                  linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
              have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_180 y (by linarith) (by linarith)
              have hw3 : (55964847/10000000000000:ℝ) ≤ wfun (x + y) := wc_451 (x + y) (by linarith) (by linarith)
              have hw4 : (23941523/1250000000000:ℝ) ≤ wfun (y + z) := wc_531 (y + z) (by linarith) (by linarith)
              have hw5 : (963306969/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1148 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (4057/2048:ℝ) with hc | hc
          · rcases le_total z (2161/2048:ℝ) with hc | hc
            · rcases le_total x (4307/4096:ℝ) with hc | hc
              · rcases le_total y (8109/4096:ℝ) with hc | hc
                · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
                  have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_162 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_449 (x + y) (by linarith) (by linarith)
                  have hw4 : (5774823/625000000000:ℝ) ≤ wfun (y + z) := wc_480 (y + z) (by linarith) (by linarith)
                  have hw5 : (1800648153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1131 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
                  have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_172 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_465 (x + y) (by linarith) (by linarith)
                  have hw4 : (569617/50000000000:ℝ) ≤ wfun (y + z) := wc_507 (y + z) (by linarith) (by linarith)
                  have hw5 : (1865416811/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1141 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
                have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_163 y (by linarith) (by linarith)
                have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                have hw3 : (18276411/2500000000000:ℝ) ≤ wfun (x + y) := wc_466 (x + y) (by linarith) (by linarith)
                have hw4 : (92247841/10000000000000:ℝ) ≤ wfun (y + z) := wc_481 (y + z) (by linarith) (by linarith)
                have hw5 : (1863183413/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1142 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
              have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_163 y (by linarith) (by linarith)
              have hw3 : (55964847/10000000000000:ℝ) ≤ wfun (x + y) := wc_451 (x + y) (by linarith) (by linarith)
              have hw4 : (13745521/1000000000000:ℝ) ≤ wfun (y + z) := wc_517 (y + z) (by linarith) (by linarith)
              have hw5 : (963306969/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1148 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (2161/2048:ℝ) with hc | hc
            · rcases le_total x (4307/4096:ℝ) with hc | hc
              · rcases le_total y (8119/4096:ℝ) with hc | hc
                · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
                  have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_179 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_479 (x + y) (by linarith) (by linarith)
                  have hw4 : (4302423/312500000000:ℝ) ≤ wfun (y + z) := wc_516 (y + z) (by linarith) (by linarith)
                  have hw5 : (965616743/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1146 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
                  have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_506 (x + y) (by linarith) (by linarith)
                  have hw4 : (163652657/10000000000000:ℝ) ≤ wfun (y + z) := wc_524 (y + z) (by linarith) (by linarith)
                  have hw5 : (49952307/250000000000:ℝ) ≤ wfun (x + y + z) := wc_1159 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
                have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_180 y (by linarith) (by linarith)
                have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                have hw3 : (569617/50000000000:ℝ) ≤ wfun (x + y) := wc_507 (x + y) (by linarith) (by linarith)
                have hw4 : (13745521/1000000000000:ℝ) ≤ wfun (y + z) := wc_517 (y + z) (by linarith) (by linarith)
                have hw5 : (1995701471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1160 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
              have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_180 y (by linarith) (by linarith)
              have hw3 : (92247841/10000000000000:ℝ) ≤ wfun (x + y) := wc_481 (x + y) (by linarith) (by linarith)
              have hw4 : (23941523/1250000000000:ℝ) ≤ wfun (y + z) := wc_531 (y + z) (by linarith) (by linarith)
              have hw5 : (2061048329/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1164 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (2151/2048:ℝ) with hc | hc
        · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
          have hw1 : (200253263/500000000000:ℝ) ≤ wfun y := wc_164 y (by linarith) (by linarith)
          have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_98 z (by linarith) (by linarith)
          have hw3 : (7141617/2500000000000:ℝ) ≤ wfun (x + y) := wc_420 (x + y) (by linarith) (by linarith)
          have hw4 : (190300253/10000000000000:ℝ) ≤ wfun (y + z) := wc_533 (y + z) (by linarith) (by linarith)
          have hw5 : (1917416231/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1150 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
          have hw1 : (200253263/500000000000:ℝ) ≤ wfun y := wc_164 y (by linarith) (by linarith)
          have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_98 z (by linarith) (by linarith)
          have hw3 : (27892031/5000000000000:ℝ) ≤ wfun (x + y) := wc_452 (x + y) (by linarith) (by linarith)
          have hw4 : (190300253/10000000000000:ℝ) ≤ wfun (y + z) := wc_533 (y + z) (by linarith) (by linarith)
          have hw5 : (410242943/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1166 (x + y + z) (by linarith) (by linarith)
          linarith
    · rcases le_total z (1083/1024:ℝ) with hc | hc
      · rcases le_total x (2151/2048:ℝ) with hc | hc
        · rcases le_total y (4067/2048:ℝ) with hc | hc
          · rcases le_total z (2161/2048:ℝ) with hc | hc
            · rcases le_total x (4297/4096:ℝ) with hc | hc
              · rcases le_total y (8129/4096:ℝ) with hc | hc
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                  have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_479 (x + y) (by linarith) (by linarith)
                  have hw4 : (47960431/2500000000000:ℝ) ≤ wfun (y + z) := wc_530 (y + z) (by linarith) (by linarith)
                  have hw5 : (965616743/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1146 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                  have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_506 (x + y) (by linarith) (by linarith)
                  have hw4 : (111118793/5000000000000:ℝ) ≤ wfun (y + z) := wc_540 (y + z) (by linarith) (by linarith)
                  have hw5 : (49952307/250000000000:ℝ) ≤ wfun (x + y + z) := wc_1159 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
                have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_195 y (by linarith) (by linarith)
                have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                have hw3 : (569617/50000000000:ℝ) ≤ wfun (x + y) := wc_507 (x + y) (by linarith) (by linarith)
                have hw4 : (23941523/1250000000000:ℝ) ≤ wfun (y + z) := wc_531 (y + z) (by linarith) (by linarith)
                have hw5 : (1995701471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1160 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
              have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_195 y (by linarith) (by linarith)
              have hw3 : (92247841/10000000000000:ℝ) ≤ wfun (x + y) := wc_481 (x + y) (by linarith) (by linarith)
              have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_544 (y + z) (by linarith) (by linarith)
              have hw5 : (2061048329/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1164 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (2161/2048:ℝ) with hc | hc
            · rcases le_total x (4297/4096:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_210 y (by linarith) (by linarith)
                have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                have hw3 : (4302423/312500000000:ℝ) ≤ wfun (x + y) := wc_516 (x + y) (by linarith) (by linarith)
                have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_544 (y + z) (by linarith) (by linarith)
                have hw5 : (103175797/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1163 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
                have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_210 y (by linarith) (by linarith)
                have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                have hw3 : (163652657/10000000000000:ℝ) ≤ wfun (x + y) := wc_524 (x + y) (by linarith) (by linarith)
                have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_544 (y + z) (by linarith) (by linarith)
                have hw5 : (426471879/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1168 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
              have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_210 y (by linarith) (by linarith)
              have hw3 : (13745521/1000000000000:ℝ) ≤ wfun (x + y) := wc_517 (x + y) (by linarith) (by linarith)
              have hw4 : (326066581/10000000000000:ℝ) ≤ wfun (y + z) := wc_552 (y + z) (by linarith) (by linarith)
              have hw5 : (1099796941/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1169 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (4067/2048:ℝ) with hc | hc
          · rcases le_total z (2161/2048:ℝ) with hc | hc
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
              have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_195 y (by linarith) (by linarith)
              have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
              have hw3 : (13745521/1000000000000:ℝ) ≤ wfun (x + y) := wc_517 (x + y) (by linarith) (by linarith)
              have hw4 : (23941523/1250000000000:ℝ) ≤ wfun (y + z) := wc_531 (y + z) (by linarith) (by linarith)
              have hw5 : (2061048329/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1164 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
              have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_195 y (by linarith) (by linarith)
              have hw3 : (13745521/1000000000000:ℝ) ≤ wfun (x + y) := wc_517 (x + y) (by linarith) (by linarith)
              have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_544 (y + z) (by linarith) (by linarith)
              have hw5 : (1099796941/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1169 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
            have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_210 y (by linarith) (by linarith)
            have hw3 : (23941523/1250000000000:ℝ) ≤ wfun (x + y) := wc_531 (x + y) (by linarith) (by linarith)
            have hw4 : (63400731/2500000000000:ℝ) ≤ wfun (y + z) := wc_545 (y + z) (by linarith) (by linarith)
            have hw5 : (2194341861/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1170 (x + y + z) (by linarith) (by linarith)
            linarith
      · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
        have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_196 y (by linarith) (by linarith)
        have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_98 z (by linarith) (by linarith)
        have hw3 : (11456693/1250000000000:ℝ) ≤ wfun (x + y) := wc_483 (x + y) (by linarith) (by linarith)
        have hw4 : (161986357/5000000000000:ℝ) ≤ wfun (y + z) := wc_554 (y + z) (by linarith) (by linarith)
        have hw5 : (272985599/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1172 (x + y + z) (by linarith) (by linarith)
        linarith

set_option maxHeartbeats 20000000 in
lemma ch_180 (x y z : ℝ) (hx1 : (131/128:ℝ) ≤ x) (hx2 : x ≤ (17/16:ℝ))
    (hy1 : (257/128:ℝ) ≤ y) (hy2 : y ≤ (131/64:ℝ))
    (hz1 : (63/64:ℝ) ≤ z) (hz2 : z ≤ (17/16:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
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
      have hw3 : (21491553/2500000000000:ℝ) ≤ wfun (x + y) := wc_488 (x + y) (by linarith) (by linarith)
      have hw5 : (59421/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_706 (x + y + z) (by linarith) (by linarith)
      linarith
    · have hw2 : (2370342229/2500000000000:ℝ) ≤ wfun z := by
        rcases le_total z (1:ℝ) with hq20 | hq20
        · exact le_trans (by norm_num) (wc_5 z (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_7 z (by linarith) (by linarith))
      have hw3 : (162913869/2500000000000:ℝ) ≤ wfun (x + y) := wc_576 (x + y) (by linarith) (by linarith)
      have hw5 : (153865963/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_788 (x + y + z) (by linarith) (by linarith)
      linarith
  · rcases le_total x (267/256:ℝ) with hc | hc
    · rcases le_total y (519/256:ℝ) with hc | hc
      · rcases le_total z (267/256:ℝ) with hc | hc
        · rcases le_total x (529/512:ℝ) with hc | hc
          · rcases le_total y (1033/512:ℝ) with hc | hc
            · rcases le_total z (529/512:ℝ) with hc | hc
              · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
                have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_243 y (by linarith) (by linarith)
                have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
                have hw3 : (18095851/2000000000000:ℝ) ≤ wfun (x + y) := wc_485 (x + y) (by linarith) (by linarith)
                have hw4 : (18095851/2000000000000:ℝ) ≤ wfun (y + z) := wc_485 (y + z) (by linarith) (by linarith)
                have hw5 : (636617867/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_826 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total x (1053/1024:ℝ) with hc | hc
                · have hw0 : (3436255003/5000000000000:ℝ) ≤ wfun x := wc_11 x (by linarith) (by linarith)
                  have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_243 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_19 z (by linarith) (by linarith)
                  have hw3 : (91064031/10000000000000:ℝ) ≤ wfun (x + y) := wc_484 (x + y) (by linarith) (by linarith)
                  have hw4 : (63967043/2000000000000:ℝ) ≤ wfun (y + z) := wc_556 (y + z) (by linarith) (by linarith)
                  have hw5 : (197587481/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_879 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_15 x (by linarith) (by linarith)
                  have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_243 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_19 z (by linarith) (by linarith)
                  have hw3 : (189078223/10000000000000:ℝ) ≤ wfun (x + y) := wc_534 (x + y) (by linarith) (by linarith)
                  have hw4 : (63967043/2000000000000:ℝ) ≤ wfun (y + z) := wc_556 (y + z) (by linarith) (by linarith)
                  have hw5 : (74301831/625000000000:ℝ) ≤ wfun (x + y + z) := wc_931 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total z (529/512:ℝ) with hc | hc
              · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
                have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_248 y (by linarith) (by linarith)
                have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
                have hw3 : (63967043/2000000000000:ℝ) ≤ wfun (x + y) := wc_556 (x + y) (by linarith) (by linarith)
                have hw4 : (63967043/2000000000000:ℝ) ≤ wfun (y + z) := wc_556 (y + z) (by linarith) (by linarith)
                have hw5 : (49160907/500000000000:ℝ) ≤ wfun (x + y + z) := wc_880 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
                have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_248 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_19 z (by linarith) (by linarith)
                have hw3 : (63967043/2000000000000:ℝ) ≤ wfun (x + y) := wc_556 (x + y) (by linarith) (by linarith)
                have hw4 : (685641829/10000000000000:ℝ) ≤ wfun (y + z) := wc_572 (y + z) (by linarith) (by linarith)
                have hw5 : (140043451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_1020 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (1033/512:ℝ) with hc | hc
            · rcases le_total z (529/512:ℝ) with hc | hc
              · rcases le_total x (1063/1024:ℝ) with hc | hc
                · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
                  have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_243 y (by linarith) (by linarith)
                  have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
                  have hw3 : (160947823/5000000000000:ℝ) ≤ wfun (x + y) := wc_555 (x + y) (by linarith) (by linarith)
                  have hw4 : (18095851/2000000000000:ℝ) ≤ wfun (y + z) := wc_485 (y + z) (by linarith) (by linarith)
                  have hw5 : (197587481/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_879 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                  have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_243 y (by linarith) (by linarith)
                  have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
                  have hw3 : (489049523/10000000000000:ℝ) ≤ wfun (x + y) := wc_565 (x + y) (by linarith) (by linarith)
                  have hw4 : (18095851/2000000000000:ℝ) ≤ wfun (y + z) := wc_485 (y + z) (by linarith) (by linarith)
                  have hw5 : (74301831/625000000000:ℝ) ≤ wfun (x + y + z) := wc_931 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total x (1063/1024:ℝ) with hc | hc
                · rcases le_total y (2061/1024:ℝ) with hc | hc
                  · rcases le_total z (1063/1024:ℝ) with hc | hc
                    · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
                      have hw1 : (543159341/10000000000000:ℝ) ≤ wfun y := wc_242 y (by linarith) (by linarith)
                      have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
                      have hw3 : (161986357/5000000000000:ℝ) ≤ wfun (x + y) := wc_554 (x + y) (by linarith) (by linarith)
                      have hw4 : (161986357/5000000000000:ℝ) ≤ wfun (y + z) := wc_554 (y + z) (by linarith) (by linarith)
                      have hw5 : (1420672477/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1017 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
                      have hw1 : (543159341/10000000000000:ℝ) ≤ wfun y := wc_242 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
                      have hw3 : (161986357/5000000000000:ℝ) ≤ wfun (x + y) := wc_554 (x + y) (by linarith) (by linarith)
                      have hw4 : (24610003/500000000000:ℝ) ≤ wfun (y + z) := wc_564 (y + z) (by linarith) (by linarith)
                      have hw5 : (1658311191/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1108 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
                    have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_246 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_19 z (by linarith) (by linarith)
                    have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_564 (x + y) (by linarith) (by linarith)
                    have hw4 : (489049523/10000000000000:ℝ) ≤ wfun (y + z) := wc_565 (y + z) (by linarith) (by linarith)
                    have hw5 : (12893743/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1109 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total y (2061/1024:ℝ) with hc | hc
                  · rcases le_total z (1063/1024:ℝ) with hc | hc
                    · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                      have hw1 : (543159341/10000000000000:ℝ) ≤ wfun y := wc_242 y (by linarith) (by linarith)
                      have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
                      have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_564 (x + y) (by linarith) (by linarith)
                      have hw4 : (161986357/5000000000000:ℝ) ≤ wfun (y + z) := wc_554 (y + z) (by linarith) (by linarith)
                      have hw5 : (1658311191/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1108 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                      have hw1 : (543159341/10000000000000:ℝ) ≤ wfun y := wc_242 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
                      have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_564 (x + y) (by linarith) (by linarith)
                      have hw4 : (24610003/500000000000:ℝ) ≤ wfun (y + z) := wc_564 (y + z) (by linarith) (by linarith)
                      have hw5 : (1912837973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1151 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                    have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_246 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_19 z (by linarith) (by linarith)
                    have hw3 : (694482783/10000000000000:ℝ) ≤ wfun (x + y) := wc_570 (x + y) (by linarith) (by linarith)
                    have hw4 : (489049523/10000000000000:ℝ) ≤ wfun (y + z) := wc_565 (y + z) (by linarith) (by linarith)
                    have hw5 : (951861201/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1152 (x + y + z) (by linarith) (by linarith)
                    linarith
            · rcases le_total z (529/512:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
                have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_248 y (by linarith) (by linarith)
                have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
                have hw3 : (685641829/10000000000000:ℝ) ≤ wfun (x + y) := wc_572 (x + y) (by linarith) (by linarith)
                have hw4 : (63967043/2000000000000:ℝ) ≤ wfun (y + z) := wc_556 (y + z) (by linarith) (by linarith)
                have hw5 : (140043451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_1020 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
                have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_248 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_19 z (by linarith) (by linarith)
                have hw3 : (685641829/10000000000000:ℝ) ≤ wfun (x + y) := wc_572 (x + y) (by linarith) (by linarith)
                have hw4 : (685641829/10000000000000:ℝ) ≤ wfun (y + z) := wc_572 (y + z) (by linarith) (by linarith)
                have hw5 : (942826837/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1154 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (529/512:ℝ) with hc | hc
          · rcases le_total y (1033/512:ℝ) with hc | hc
            · rcases le_total z (539/512:ℝ) with hc | hc
              · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
                have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_243 y (by linarith) (by linarith)
                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_41 z (by linarith) (by linarith)
                have hw3 : (18095851/2000000000000:ℝ) ≤ wfun (x + y) := wc_485 (x + y) (by linarith) (by linarith)
                have hw4 : (685641829/10000000000000:ℝ) ≤ wfun (y + z) := wc_572 (y + z) (by linarith) (by linarith)
                have hw5 : (140043451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_1020 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
                have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_243 y (by linarith) (by linarith)
                have hw3 : (18095851/2000000000000:ℝ) ≤ wfun (x + y) := wc_485 (x + y) (by linarith) (by linarith)
                have hw4 : (591930551/5000000000000:ℝ) ≤ wfun (y + z) := wc_584 (y + z) (by linarith) (by linarith)
                have hw5 : (942826837/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1154 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
              have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_248 y (by linarith) (by linarith)
              have hw3 : (63967043/2000000000000:ℝ) ≤ wfun (x + y) := wc_556 (x + y) (by linarith) (by linarith)
              have hw4 : (1168886057/10000000000000:ℝ) ≤ wfun (y + z) := wc_585 (y + z) (by linarith) (by linarith)
              have hw5 : (933899467/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1155 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (1033/512:ℝ) with hc | hc
            · rcases le_total z (539/512:ℝ) with hc | hc
              · rcases le_total x (1063/1024:ℝ) with hc | hc
                · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
                  have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_243 y (by linarith) (by linarith)
                  have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_41 z (by linarith) (by linarith)
                  have hw3 : (160947823/5000000000000:ℝ) ≤ wfun (x + y) := wc_555 (x + y) (by linarith) (by linarith)
                  have hw4 : (685641829/10000000000000:ℝ) ≤ wfun (y + z) := wc_572 (y + z) (by linarith) (by linarith)
                  have hw5 : (947330549/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1153 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total y (2061/1024:ℝ) with hc | hc
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                    have hw1 : (543159341/10000000000000:ℝ) ≤ wfun y := wc_242 y (by linarith) (by linarith)
                    have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_41 z (by linarith) (by linarith)
                    have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_564 (x + y) (by linarith) (by linarith)
                    have hw4 : (172511147/2500000000000:ℝ) ≤ wfun (y + z) := wc_571 (y + z) (by linarith) (by linarith)
                    have hw5 : (271686247/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1173 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                    have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_246 y (by linarith) (by linarith)
                    have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_41 z (by linarith) (by linarith)
                    have hw3 : (694482783/10000000000000:ℝ) ≤ wfun (x + y) := wc_570 (x + y) (by linarith) (by linarith)
                    have hw4 : (924357731/10000000000000:ℝ) ≤ wfun (y + z) := wc_581 (y + z) (by linarith) (by linarith)
                    have hw5 : (1229661173/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1180 (x + y + z) (by linarith) (by linarith)
                    linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
                have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_243 y (by linarith) (by linarith)
                have hw3 : (63967043/2000000000000:ℝ) ≤ wfun (x + y) := wc_556 (x + y) (by linarith) (by linarith)
                have hw4 : (591930551/5000000000000:ℝ) ≤ wfun (y + z) := wc_584 (y + z) (by linarith) (by linarith)
                have hw5 : (1218017847/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1182 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
              have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_248 y (by linarith) (by linarith)
              have hw3 : (685641829/10000000000000:ℝ) ≤ wfun (x + y) := wc_572 (x + y) (by linarith) (by linarith)
              have hw4 : (1168886057/10000000000000:ℝ) ≤ wfun (y + z) := wc_585 (y + z) (by linarith) (by linarith)
              have hw5 : (2413024171/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1183 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (267/256:ℝ) with hc | hc
        · rcases le_total x (529/512:ℝ) with hc | hc
          · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
            have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_13 z (by linarith) (by linarith)
            have hw3 : (676941261/10000000000000:ℝ) ≤ wfun (x + y) := wc_573 (x + y) (by linarith) (by linarith)
            have hw4 : (66837841/1000000000000:ℝ) ≤ wfun (y + z) := wc_574 (y + z) (by linarith) (by linarith)
            have hw5 : (274801629/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1022 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
            have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_13 z (by linarith) (by linarith)
            have hw3 : (1168886057/10000000000000:ℝ) ≤ wfun (x + y) := wc_585 (x + y) (by linarith) (by linarith)
            have hw4 : (66837841/1000000000000:ℝ) ≤ wfun (y + z) := wc_574 (y + z) (by linarith) (by linarith)
            have hw5 : (1850155147/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1156 (x + y + z) (by linarith) (by linarith)
            linarith
        · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
          have hw3 : (66837841/1000000000000:ℝ) ≤ wfun (x + y) := wc_574 (x + y) (by linarith) (by linarith)
          have hw4 : (1764735511/10000000000000:ℝ) ≤ wfun (y + z) := wc_590 (y + z) (by linarith) (by linarith)
          have hw5 : (591952751/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1184 (x + y + z) (by linarith) (by linarith)
          linarith
    · rcases le_total y (519/256:ℝ) with hc | hc
      · rcases le_total z (267/256:ℝ) with hc | hc
        · rcases le_total x (539/512:ℝ) with hc | hc
          · rcases le_total y (1033/512:ℝ) with hc | hc
            · rcases le_total z (529/512:ℝ) with hc | hc
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_243 y (by linarith) (by linarith)
                have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
                have hw3 : (685641829/10000000000000:ℝ) ≤ wfun (x + y) := wc_572 (x + y) (by linarith) (by linarith)
                have hw4 : (18095851/2000000000000:ℝ) ≤ wfun (y + z) := wc_485 (y + z) (by linarith) (by linarith)
                have hw5 : (140043451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_1020 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total x (1073/1024:ℝ) with hc | hc
                · rcases le_total y (2061/1024:ℝ) with hc | hc
                  · rcases le_total z (1063/1024:ℝ) with hc | hc
                    · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
                      have hw1 : (543159341/10000000000000:ℝ) ≤ wfun y := wc_242 y (by linarith) (by linarith)
                      have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
                      have hw3 : (694482783/10000000000000:ℝ) ≤ wfun (x + y) := wc_570 (x + y) (by linarith) (by linarith)
                      have hw4 : (161986357/5000000000000:ℝ) ≤ wfun (y + z) := wc_554 (y + z) (by linarith) (by linarith)
                      have hw5 : (1912837973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1151 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
                      have hw1 : (543159341/10000000000000:ℝ) ≤ wfun y := wc_242 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
                      have hw3 : (694482783/10000000000000:ℝ) ≤ wfun (x + y) := wc_570 (x + y) (by linarith) (by linarith)
                      have hw4 : (24610003/500000000000:ℝ) ≤ wfun (y + z) := wc_564 (y + z) (by linarith) (by linarith)
                      have hw5 : (272985599/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1172 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
                    have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_246 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_19 z (by linarith) (by linarith)
                    have hw3 : (930293373/10000000000000:ℝ) ≤ wfun (x + y) := wc_580 (x + y) (by linarith) (by linarith)
                    have hw4 : (489049523/10000000000000:ℝ) ≤ wfun (y + z) := wc_565 (y + z) (by linarith) (by linarith)
                    have hw5 : (271686247/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1173 (x + y + z) (by linarith) (by linarith)
                    linarith
                · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
                  have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_243 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_19 z (by linarith) (by linarith)
                  have hw3 : (924357731/10000000000000:ℝ) ≤ wfun (x + y) := wc_581 (x + y) (by linarith) (by linarith)
                  have hw4 : (63967043/2000000000000:ℝ) ≤ wfun (y + z) := wc_556 (y + z) (by linarith) (by linarith)
                  have hw5 : (216315697/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_1174 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total z (529/512:ℝ) with hc | hc
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_248 y (by linarith) (by linarith)
                have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
                have hw3 : (591930551/5000000000000:ℝ) ≤ wfun (x + y) := wc_584 (x + y) (by linarith) (by linarith)
                have hw4 : (63967043/2000000000000:ℝ) ≤ wfun (y + z) := wc_556 (y + z) (by linarith) (by linarith)
                have hw5 : (942826837/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1154 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_248 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_19 z (by linarith) (by linarith)
                have hw3 : (591930551/5000000000000:ℝ) ≤ wfun (x + y) := wc_584 (x + y) (by linarith) (by linarith)
                have hw4 : (685641829/10000000000000:ℝ) ≤ wfun (y + z) := wc_572 (y + z) (by linarith) (by linarith)
                have hw5 : (1218017847/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1182 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (1033/512:ℝ) with hc | hc
            · rcases le_total z (529/512:ℝ) with hc | hc
              · have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_243 y (by linarith) (by linarith)
                have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
                have hw3 : (591930551/5000000000000:ℝ) ≤ wfun (x + y) := wc_584 (x + y) (by linarith) (by linarith)
                have hw4 : (18095851/2000000000000:ℝ) ≤ wfun (y + z) := wc_485 (y + z) (by linarith) (by linarith)
                have hw5 : (942826837/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1154 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_243 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_19 z (by linarith) (by linarith)
                have hw3 : (591930551/5000000000000:ℝ) ≤ wfun (x + y) := wc_584 (x + y) (by linarith) (by linarith)
                have hw4 : (63967043/2000000000000:ℝ) ≤ wfun (y + z) := wc_556 (y + z) (by linarith) (by linarith)
                have hw5 : (1218017847/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1182 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_248 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_13 z (by linarith) (by linarith)
              have hw3 : (1810022563/10000000000000:ℝ) ≤ wfun (x + y) := wc_589 (x + y) (by linarith) (by linarith)
              have hw4 : (157881813/5000000000000:ℝ) ≤ wfun (y + z) := wc_557 (y + z) (by linarith) (by linarith)
              have hw5 : (2413024171/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1183 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (539/512:ℝ) with hc | hc
          · rcases le_total y (1033/512:ℝ) with hc | hc
            · rcases le_total z (539/512:ℝ) with hc | hc
              · rcases le_total x (1073/1024:ℝ) with hc | hc
                · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
                  have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_243 y (by linarith) (by linarith)
                  have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_41 z (by linarith) (by linarith)
                  have hw3 : (172511147/2500000000000:ℝ) ≤ wfun (x + y) := wc_571 (x + y) (by linarith) (by linarith)
                  have hw4 : (685641829/10000000000000:ℝ) ≤ wfun (y + z) := wc_572 (y + z) (by linarith) (by linarith)
                  have hw5 : (2447644383/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1181 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
                  have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_243 y (by linarith) (by linarith)
                  have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_41 z (by linarith) (by linarith)
                  have hw3 : (924357731/10000000000000:ℝ) ≤ wfun (x + y) := wc_581 (x + y) (by linarith) (by linarith)
                  have hw4 : (685641829/10000000000000:ℝ) ≤ wfun (y + z) := wc_572 (y + z) (by linarith) (by linarith)
                  have hw5 : (549546581/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1191 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_243 y (by linarith) (by linarith)
                have hw3 : (685641829/10000000000000:ℝ) ≤ wfun (x + y) := wc_572 (x + y) (by linarith) (by linarith)
                have hw4 : (591930551/5000000000000:ℝ) ≤ wfun (y + z) := wc_584 (y + z) (by linarith) (by linarith)
                have hw5 : (3048526697/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1193 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
              have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_248 y (by linarith) (by linarith)
              have hw3 : (591930551/5000000000000:ℝ) ≤ wfun (x + y) := wc_584 (x + y) (by linarith) (by linarith)
              have hw4 : (1168886057/10000000000000:ℝ) ≤ wfun (y + z) := wc_585 (y + z) (by linarith) (by linarith)
              have hw5 : (3019797449/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1194 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_244 y (by linarith) (by linarith)
            have hw3 : (1168886057/10000000000000:ℝ) ≤ wfun (x + y) := wc_585 (x + y) (by linarith) (by linarith)
            have hw4 : (66837841/1000000000000:ℝ) ≤ wfun (y + z) := wc_574 (y + z) (by linarith) (by linarith)
            have hw5 : (2991406031/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1195 (x + y + z) (by linarith) (by linarith)
            linarith
      · have hw3 : (1764735511/10000000000000:ℝ) ≤ wfun (x + y) := wc_590 (x + y) (by linarith) (by linarith)
        have hw4 : (162913869/2500000000000:ℝ) ≤ wfun (y + z) := wc_576 (y + z) (by linarith) (by linarith)
        have hw5 : (1161826227/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1185 (x + y + z) (by linarith) (by linarith)
        linarith

set_option maxHeartbeats 20000000 in
lemma ch_189 (x y z : ℝ) (hx1 : (267/256:ℝ) ≤ x) (hx2 : x ≤ (17/16:ℝ))
    (hy1 : (63/32:ℝ) ≤ y) (hy2 : y ≤ (509/256:ℝ))
    (hz1 : (257/128:ℝ) ≤ z) (hz2 : z ≤ (131/64:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total z (519/256:ℝ) with hc | hc
  · rcases le_total x (539/512:ℝ) with hc | hc
    · rcases le_total y (1013/512:ℝ) with hc | hc
      · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
        have hw1 : (4884069333/10000000000000:ℝ) ≤ wfun y := wc_132 y (by linarith) (by linarith)
        have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_244 z (by linarith) (by linarith)
        have hw4 : (19058233/5000000000000:ℝ) ≤ wfun (y + z) := by
          rcases le_total (y + z) (4:ℝ) with hq40 | hq40
          · exact le_trans (by norm_num) (wc_643 (y + z) (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_668 (y + z) (by linarith) (by linarith))
        have hw5 : (3568011/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1220 (x + y + z) (by linarith) (by linarith)
        linarith
      · rcases le_total z (1033/512:ℝ) with hc | hc
        · rcases le_total x (1073/1024:ℝ) with hc | hc
          · rcases le_total y (2031/1024:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (200253263/500000000000:ℝ) ≤ wfun y := wc_164 y (by linarith) (by linarith)
              have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_243 z (by linarith) (by linarith)
              have hw3 : (293481/2500000000000:ℝ) ≤ wfun (x + y) := wc_363 (x + y) (by linarith) (by linarith)
              have hw4 : (11042139/1250000000000:ℝ) ≤ wfun (y + z) := by
                rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                · exact le_trans (by norm_num) (wc_650 (y + z) (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_661 (y + z) (by linarith) (by linarith))
              have hw5 : (314267/40000000000:ℝ) ≤ wfun (x + y + z) := wc_1238 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (2061/1024:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
                have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_196 y (by linarith) (by linarith)
                have hw2 : (543159341/10000000000000:ℝ) ≤ wfun z := wc_242 z (by linarith) (by linarith)
                have hw3 : (28474189/10000000000000:ℝ) ≤ wfun (x + y) := wc_421 (x + y) (by linarith) (by linarith)
                have hw4 : (11042139/1250000000000:ℝ) ≤ wfun (y + z) := by
                  rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                  · exact le_trans (by norm_num) (wc_653 (y + z) (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_661 (y + z) (by linarith) (by linarith))
                have hw5 : (16256217/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1247 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
                have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_196 y (by linarith) (by linarith)
                have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_246 z (by linarith) (by linarith)
                have hw3 : (28474189/10000000000000:ℝ) ≤ wfun (x + y) := wc_421 (x + y) (by linarith) (by linarith)
                have hw4 : (19058233/5000000000000:ℝ) ≤ wfun (y + z) := by
                  rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                  · exact le_trans (by norm_num) (wc_656 (y + z) (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_668 (y + z) (by linarith) (by linarith))
                have hw5 : (38749297/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1262 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (2031/1024:ℝ) with hc | hc
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
              have hw1 : (200253263/500000000000:ℝ) ≤ wfun y := wc_164 y (by linarith) (by linarith)
              have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_243 z (by linarith) (by linarith)
              have hw3 : (28474189/10000000000000:ℝ) ≤ wfun (x + y) := wc_421 (x + y) (by linarith) (by linarith)
              have hw4 : (11042139/1250000000000:ℝ) ≤ wfun (y + z) := by
                rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                · exact le_trans (by norm_num) (wc_650 (y + z) (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_661 (y + z) (by linarith) (by linarith))
              have hw5 : (6477343/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1249 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (2061/1024:ℝ) with hc | hc
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
                have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_196 y (by linarith) (by linarith)
                have hw2 : (543159341/10000000000000:ℝ) ≤ wfun z := wc_242 z (by linarith) (by linarith)
                have hw3 : (11456693/1250000000000:ℝ) ≤ wfun (x + y) := wc_483 (x + y) (by linarith) (by linarith)
                have hw4 : (11042139/1250000000000:ℝ) ≤ wfun (y + z) := by
                  rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                  · exact le_trans (by norm_num) (wc_653 (y + z) (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_661 (y + z) (by linarith) (by linarith))
                have hw5 : (38749297/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1262 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total x (2151/2048:ℝ) with hc | hc
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
                  have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_196 y (by linarith) (by linarith)
                  have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_246 z (by linarith) (by linarith)
                  have hw3 : (22987523/2500000000000:ℝ) ≤ wfun (x + y) := wc_482 (x + y) (by linarith) (by linarith)
                  have hw4 : (19058233/5000000000000:ℝ) ≤ wfun (y + z) := by
                    rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                    · exact le_trans (by norm_num) (wc_656 (y + z) (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_668 (y + z) (by linarith) (by linarith))
                  have hw5 : (67587843/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1286 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
                  have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_196 y (by linarith) (by linarith)
                  have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_246 z (by linarith) (by linarith)
                  have hw3 : (2140811/156250000000:ℝ) ≤ wfun (x + y) := wc_518 (x + y) (by linarith) (by linarith)
                  have hw4 : (19058233/5000000000000:ℝ) ≤ wfun (y + z) := by
                    rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                    · exact le_trans (by norm_num) (wc_656 (y + z) (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_668 (y + z) (by linarith) (by linarith))
                  have hw5 : (12522987/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1301 (x + y + z) (by linarith) (by linarith)
                  linarith
        · rcases le_total x (1073/1024:ℝ) with hc | hc
          · rcases le_total y (2031/1024:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (200253263/500000000000:ℝ) ≤ wfun y := wc_164 y (by linarith) (by linarith)
              have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_248 z (by linarith) (by linarith)
              have hw3 : (293481/2500000000000:ℝ) ≤ wfun (x + y) := wc_363 (x + y) (by linarith) (by linarith)
              have hw4 : (436723/500000000000:ℝ) ≤ wfun (y + z) := by
                rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                · exact le_trans (by norm_num) (wc_656 (y + z) (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_673 (y + z) (by linarith) (by linarith))
              have hw5 : (12062377/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1264 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_196 y (by linarith) (by linarith)
              have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_248 z (by linarith) (by linarith)
              have hw3 : (28474189/10000000000000:ℝ) ≤ wfun (x + y) := wc_421 (x + y) (by linarith) (by linarith)
              have hw5 : (53757489/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1290 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (2031/1024:ℝ) with hc | hc
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
              have hw1 : (200253263/500000000000:ℝ) ≤ wfun y := wc_164 y (by linarith) (by linarith)
              have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_248 z (by linarith) (by linarith)
              have hw3 : (28474189/10000000000000:ℝ) ≤ wfun (x + y) := wc_421 (x + y) (by linarith) (by linarith)
              have hw4 : (436723/500000000000:ℝ) ≤ wfun (y + z) := by
                rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                · exact le_trans (by norm_num) (wc_656 (y + z) (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_673 (y + z) (by linarith) (by linarith))
              have hw5 : (53757489/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1290 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (2071/1024:ℝ) with hc | hc
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
                have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_196 y (by linarith) (by linarith)
                have hw2 : (103168503/10000000000000:ℝ) ≤ wfun z := wc_247 z (by linarith) (by linarith)
                have hw3 : (11456693/1250000000000:ℝ) ≤ wfun (x + y) := wc_483 (x + y) (by linarith) (by linarith)
                have hw4 : (436723/500000000000:ℝ) ≤ wfun (y + z) := wc_680 (y + z) (by linarith) (by linarith)
                have hw5 : (358152183/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1310 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
                have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_196 y (by linarith) (by linarith)
                have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_249 z (by linarith) (by linarith)
                have hw3 : (11456693/1250000000000:ℝ) ≤ wfun (x + y) := wc_483 (x + y) (by linarith) (by linarith)
                have hw5 : (458561277/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1338 (x + y + z) (by linarith) (by linarith)
                linarith
    · rcases le_total y (1013/512:ℝ) with hc | hc
      · have hw1 : (4884069333/10000000000000:ℝ) ≤ wfun y := wc_132 y (by linarith) (by linarith)
        have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_244 z (by linarith) (by linarith)
        have hw3 : (231767/2000000000000:ℝ) ≤ wfun (x + y) := wc_365 (x + y) (by linarith) (by linarith)
        have hw4 : (19058233/5000000000000:ℝ) ≤ wfun (y + z) := by
          rcases le_total (y + z) (4:ℝ) with hq40 | hq40
          · exact le_trans (by norm_num) (wc_643 (y + z) (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_668 (y + z) (by linarith) (by linarith))
        have hw5 : (38680157/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1241 (x + y + z) (by linarith) (by linarith)
        linarith
      · rcases le_total z (1033/512:ℝ) with hc | hc
        · rcases le_total x (1083/1024:ℝ) with hc | hc
          · rcases le_total y (2031/1024:ℝ) with hc | hc
            · have hw1 : (200253263/500000000000:ℝ) ≤ wfun y := wc_164 y (by linarith) (by linarith)
              have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_243 z (by linarith) (by linarith)
              have hw3 : (11456693/1250000000000:ℝ) ≤ wfun (x + y) := wc_483 (x + y) (by linarith) (by linarith)
              have hw4 : (11042139/1250000000000:ℝ) ≤ wfun (y + z) := by
                rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                · exact le_trans (by norm_num) (wc_650 (y + z) (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_661 (y + z) (by linarith) (by linarith))
              have hw5 : (12062377/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1264 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (2061/1024:ℝ) with hc | hc
              · have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_196 y (by linarith) (by linarith)
                have hw2 : (543159341/10000000000000:ℝ) ≤ wfun z := wc_242 z (by linarith) (by linarith)
                have hw3 : (190300253/10000000000000:ℝ) ≤ wfun (x + y) := wc_533 (x + y) (by linarith) (by linarith)
                have hw4 : (11042139/1250000000000:ℝ) ≤ wfun (y + z) := by
                  rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                  · exact le_trans (by norm_num) (wc_653 (y + z) (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_661 (y + z) (by linarith) (by linarith))
                have hw5 : (134914401/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1288 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_196 y (by linarith) (by linarith)
                have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_246 z (by linarith) (by linarith)
                have hw3 : (190300253/10000000000000:ℝ) ≤ wfun (x + y) := wc_533 (x + y) (by linarith) (by linarith)
                have hw4 : (19058233/5000000000000:ℝ) ≤ wfun (y + z) := by
                  rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                  · exact le_trans (by norm_num) (wc_656 (y + z) (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_668 (y + z) (by linarith) (by linarith))
                have hw5 : (358152183/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1310 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (2031/1024:ℝ) with hc | hc
            · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_98 x (by linarith) (by linarith)
              have hw1 : (200253263/500000000000:ℝ) ≤ wfun y := wc_164 y (by linarith) (by linarith)
              have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_243 z (by linarith) (by linarith)
              have hw3 : (190300253/10000000000000:ℝ) ≤ wfun (x + y) := wc_533 (x + y) (by linarith) (by linarith)
              have hw4 : (11042139/1250000000000:ℝ) ≤ wfun (y + z) := by
                rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                · exact le_trans (by norm_num) (wc_650 (y + z) (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_661 (y + z) (by linarith) (by linarith))
              have hw5 : (53757489/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1290 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_98 x (by linarith) (by linarith)
              have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_196 y (by linarith) (by linarith)
              have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_243 z (by linarith) (by linarith)
              have hw3 : (161986357/5000000000000:ℝ) ≤ wfun (x + y) := wc_554 (x + y) (by linarith) (by linarith)
              have hw4 : (19058233/5000000000000:ℝ) ≤ wfun (y + z) := by
                rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                · exact le_trans (by norm_num) (wc_653 (y + z) (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_668 (y + z) (by linarith) (by linarith))
              have hw5 : (356771293/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1312 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (1083/1024:ℝ) with hc | hc
          · rcases le_total y (2031/1024:ℝ) with hc | hc
            · have hw1 : (200253263/500000000000:ℝ) ≤ wfun y := wc_164 y (by linarith) (by linarith)
              have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_248 z (by linarith) (by linarith)
              have hw3 : (11456693/1250000000000:ℝ) ≤ wfun (x + y) := wc_483 (x + y) (by linarith) (by linarith)
              have hw4 : (436723/500000000000:ℝ) ≤ wfun (y + z) := by
                rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                · exact le_trans (by norm_num) (wc_656 (y + z) (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_673 (y + z) (by linarith) (by linarith))
              have hw5 : (356771293/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1312 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_196 y (by linarith) (by linarith)
              have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_248 z (by linarith) (by linarith)
              have hw3 : (190300253/10000000000000:ℝ) ≤ wfun (x + y) := wc_533 (x + y) (by linarith) (by linarith)
              have hw5 : (114198739/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1340 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_98 x (by linarith) (by linarith)
            have hw1 : (3192232409/10000000000000:ℝ) ≤ wfun y := wc_165 y (by linarith) (by linarith)
            have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_248 z (by linarith) (by linarith)
            have hw3 : (189078223/10000000000000:ℝ) ≤ wfun (x + y) := wc_534 (x + y) (by linarith) (by linarith)
            have hw5 : (91007427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1341 (x + y + z) (by linarith) (by linarith)
            linarith
  · rcases le_total x (539/512:ℝ) with hc | hc
    · rcases le_total y (1013/512:ℝ) with hc | hc
      · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
        have hw1 : (4884069333/10000000000000:ℝ) ≤ wfun y := wc_132 y (by linarith) (by linarith)
        have hw5 : (190040129/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1267 (x + y + z) (by linarith) (by linarith)
        linarith
      · rcases le_total z (1043/512:ℝ) with hc | hc
        · rcases le_total x (1073/1024:ℝ) with hc | hc
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
            have hw1 : (3192232409/10000000000000:ℝ) ≤ wfun y := wc_165 y (by linarith) (by linarith)
            have hw3 : (1166349/10000000000000:ℝ) ≤ wfun (x + y) := wc_364 (x + y) (by linarith) (by linarith)
            have hw5 : (71079411/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1313 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
            have hw1 : (3192232409/10000000000000:ℝ) ≤ wfun y := wc_165 y (by linarith) (by linarith)
            have hw3 : (28290747/10000000000000:ℝ) ≤ wfun (x + y) := wc_422 (x + y) (by linarith) (by linarith)
            have hw5 : (91007427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1341 (x + y + z) (by linarith) (by linarith)
            linarith
        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
          have hw1 : (3192232409/10000000000000:ℝ) ≤ wfun y := wc_165 y (by linarith) (by linarith)
          have hw2 : (21355581/2500000000000:ℝ) ≤ wfun z := wc_250 z (by linarith) (by linarith)
          have hw3 : (231767/2000000000000:ℝ) ≤ wfun (x + y) := wc_365 (x + y) (by linarith) (by linarith)
          have hw4 : (32087/5000000000000:ℝ) ≤ wfun (y + z) := wc_700 (y + z) (by linarith) (by linarith)
          have hw5 : (112866211/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1369 (x + y + z) (by linarith) (by linarith)
          linarith
    · rcases le_total y (1013/512:ℝ) with hc | hc
      · have hw1 : (4884069333/10000000000000:ℝ) ≤ wfun y := wc_132 y (by linarith) (by linarith)
        have hw3 : (231767/2000000000000:ℝ) ≤ wfun (x + y) := wc_365 (x + y) (by linarith) (by linarith)
        have hw5 : (43914233/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1315 (x + y + z) (by linarith) (by linarith)
        linarith
      · have hw1 : (3192232409/10000000000000:ℝ) ≤ wfun y := wc_165 y (by linarith) (by linarith)
        have hw3 : (18095851/2000000000000:ℝ) ≤ wfun (x + y) := wc_485 (x + y) (by linarith) (by linarith)
        have hw5 : (560010683/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1370 (x + y + z) (by linarith) (by linarith)
        linarith

set_option maxHeartbeats 20000000 in
lemma ch_216 (x y z : ℝ) (hx1 : (121/64:ℝ) ≤ x) (hx2 : x ≤ (131/64:ℝ))
    (hy1 : (63/64:ℝ) ≤ y) (hy2 : y ≤ (73/64:ℝ))
    (hz1 : (131/64:ℝ) ≤ z) (hz2 : z ≤ (141/64:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (63/32:ℝ) with hc | hc
  · have hw0 : (795663039/1250000000000:ℝ) ≤ wfun x := wc_117 x (by linarith) (by linarith)
    have hw2 : (182240171/5000000000000:ℝ) ≤ wfun z := wc_259 z (by linarith) (by linarith)
    have hw4 : (17540223/2500000000000:ℝ) ≤ wfun (y + z) := by
      rcases le_total (y + z) (13/4:ℝ) with hq40 | hq40
      · exact le_trans (by norm_num) (wc_493 (y + z) (by linarith) (by linarith))
      exact le_trans (by norm_num) (wc_612 (y + z) (by linarith) (by linarith))
    linarith
  · rcases le_total y (17/16:ℝ) with hc | hc
    · rcases le_total z (17/8:ℝ) with hc | hc
      · rcases le_total x (257/128:ℝ) with hc | hc
        · rcases le_total y (131/128:ℝ) with hc | hc
          · have hw0 : (179073511/2000000000000:ℝ) ≤ wfun x := by
              rcases le_total x (2:ℝ) with hq00 | hq00
              · exact le_trans (by norm_num) (wc_134 x (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_236 x (by linarith) (by linarith))
            have hw1 : (2370342229/2500000000000:ℝ) ≤ wfun y := by
              rcases le_total y (1:ℝ) with hq10 | hq10
              · exact le_trans (by norm_num) (wc_5 y (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_7 y (by linarith) (by linarith))
            have hw2 : (42177537/1000000000000:ℝ) ≤ wfun z := wc_257 z (by linarith) (by linarith)
            have hw4 : (79711817/10000000000000:ℝ) ≤ wfun (y + z) := wc_491 (y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total z (267/128:ℝ) with hc | hc
            · rcases le_total x (509/256:ℝ) with hc | hc
              · have hw0 : (396477691/1250000000000:ℝ) ≤ wfun x := wc_133 x (by linarith) (by linarith)
                have hw2 : (18186303/400000000000:ℝ) ≤ wfun z := wc_255 z (by linarith) (by linarith)
                have hw4 : (419583999/2500000000000:ℝ) ≤ wfun (y + z) := wc_592 (y + z) (by linarith) (by linarith)
                have hw5 : (90750063/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1271 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (179073511/2000000000000:ℝ) ≤ wfun x := by
                  rcases le_total x (2:ℝ) with hq00 | hq00
                  · exact le_trans (by norm_num) (wc_220 x (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_236 x (by linarith) (by linarith))
                have hw2 : (18186303/400000000000:ℝ) ≤ wfun z := wc_255 z (by linarith) (by linarith)
                have hw4 : (419583999/2500000000000:ℝ) ≤ wfun (y + z) := wc_592 (y + z) (by linarith) (by linarith)
                have hw5 : (534939039/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1374 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (179073511/2000000000000:ℝ) ≤ wfun x := by
                rcases le_total x (2:ℝ) with hq00 | hq00
                · exact le_trans (by norm_num) (wc_134 x (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_236 x (by linarith) (by linarith))
              have hw2 : (4789633321/10000000000000:ℝ) ≤ wfun z := wc_272 z (by linarith) (by linarith)
              have hw4 : (5096134953/10000000000000:ℝ) ≤ wfun (y + z) := wc_604 (y + z) (by linarith) (by linarith)
              have hw5 : (1048517003/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1474 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (131/128:ℝ) with hc | hc
          · have hw1 : (2370342229/2500000000000:ℝ) ≤ wfun y := by
              rcases le_total y (1:ℝ) with hq10 | hq10
              · exact le_trans (by norm_num) (wc_5 y (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_7 y (by linarith) (by linarith))
            have hw2 : (42177537/1000000000000:ℝ) ≤ wfun z := wc_257 z (by linarith) (by linarith)
            have hw4 : (79711817/10000000000000:ℝ) ≤ wfun (y + z) := wc_491 (y + z) (by linarith) (by linarith)
            have hw5 : (21679333/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1272 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw2 : (42177537/1000000000000:ℝ) ≤ wfun z := wc_257 z (by linarith) (by linarith)
            have hw3 : (20953831/2500000000000:ℝ) ≤ wfun (x + y) := wc_489 (x + y) (by linarith) (by linarith)
            have hw4 : (798582451/5000000000000:ℝ) ≤ wfun (y + z) := wc_594 (y + z) (by linarith) (by linarith)
            have hw5 : (1017509707/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1475 (x + y + z) (by linarith) (by linarith)
            linarith
      · have hw2 : (48584483/40000000000:ℝ) ≤ wfun z := wc_278 z (by linarith) (by linarith)
        have hw4 : (589186081/1250000000000:ℝ) ≤ wfun (y + z) := by
          rcases le_total (y + z) (13/4:ℝ) with hq40 | hq40
          · exact le_trans (by norm_num) (wc_606 (y + z) (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_609 (y + z) (by linarith) (by linarith))
        have hw5 : (502714163/5000000000000:ℝ) ≤ wfun (x + y + z) := by
          rcases le_total (x + y + z) (21/4:ℝ) with hq50 | hq50
          · exact le_trans (by norm_num) (wc_1476 (x + y + z) (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_1507 (x + y + z) (by linarith) (by linarith))
        linarith
    · have hw1 : (15429929/1000000000000:ℝ) ≤ wfun y := wc_104 y (by linarith) (by linarith)
      have hw2 : (182240171/5000000000000:ℝ) ≤ wfun z := wc_259 z (by linarith) (by linarith)
      have hw3 : (75856633/10000000000000:ℝ) ≤ wfun (x + y) := wc_492 (x + y) (by linarith) (by linarith)
      have hw4 : (589186081/1250000000000:ℝ) ≤ wfun (y + z) := by
        rcases le_total (y + z) (13/4:ℝ) with hq40 | hq40
        · exact le_trans (by norm_num) (wc_606 (y + z) (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_612 (y + z) (by linarith) (by linarith))
      have hw5 : (502714163/5000000000000:ℝ) ≤ wfun (x + y + z) := by
        rcases le_total (x + y + z) (21/4:ℝ) with hq50 | hq50
        · exact le_trans (by norm_num) (wc_1476 (x + y + z) (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_1510 (x + y + z) (by linarith) (by linarith))
      linarith

end Zeta23Ext.Bridge.FourPoint
