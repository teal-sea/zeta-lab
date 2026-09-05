import FourPoint.Chunks0
import FourPoint.Chunks1
import FourPoint.Chunks2
import FourPoint.Chunks3
import FourPoint.Chunks4
import FourPoint.Chunks5
import FourPoint.Chunks6
import FourPoint.Chunks7
import FourPoint.Chunks8
import FourPoint.Chunks9
import FourPoint.Chunks10
import FourPoint.Chunks11
import FourPoint.Chunks12
import FourPoint.Chunks13
import FourPoint.Chunks14
import FourPoint.Chunks15

/-! One router lemma per surviving box of the three-dimensional table.  The body is
the top of the box's bisection tree; every branch ends in a chunk lemma. -/

noncomputable section
namespace Zeta23Ext.Bridge.FourPoint

set_option maxHeartbeats 20000000 in
/-- The box `B1 × B1 × B1`. -/
lemma box_0_0_0 (x y z : ℝ) (hx1 : (63/64:ℝ) ≤ x) (hx2 : x ≤ (73/64:ℝ))
    (hy1 : (63/64:ℝ) ≤ y) (hy2 : y ≤ (73/64:ℝ))
    (hz1 : (63/64:ℝ) ≤ z) (hz2 : z ≤ (73/64:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  exact ch_0 x y z (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith)

set_option maxHeartbeats 20000000 in
/-- The box `B1 × B1 × B2`. -/
lemma box_0_0_1 (x y z : ℝ) (hx1 : (63/64:ℝ) ≤ x) (hx2 : x ≤ (73/64:ℝ))
    (hy1 : (63/64:ℝ) ≤ y) (hy2 : y ≤ (73/64:ℝ))
    (hz1 : (121/64:ℝ) ≤ z) (hz2 : z ≤ (141/64:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  exact ch_1 x y z (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith)

set_option maxHeartbeats 20000000 in
/-- The box `B1 × B1 × B3`. -/
lemma box_0_0_2 (x y z : ℝ) (hx1 : (63/64:ℝ) ≤ x) (hx2 : x ≤ (73/64:ℝ))
    (hy1 : (63/64:ℝ) ≤ y) (hy2 : y ≤ (73/64:ℝ))
    (hz1 : (179/64:ℝ) ≤ z) (hz2 : z ≤ (105/32:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  exact ch_2 x y z (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith)

set_option maxHeartbeats 20000000 in
/-- The box `B1 × B1 × B4`. -/
lemma box_0_0_3 (x y z : ℝ) (hx1 : (63/64:ℝ) ≤ x) (hx2 : x ≤ (73/64:ℝ))
    (hy1 : (63/64:ℝ) ≤ y) (hy2 : y ≤ (73/64:ℝ))
    (hz1 : (237/64:ℝ) ≤ z) (hz2 : z ≤ (233/40:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  exact ch_3 x y z (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith)

set_option maxHeartbeats 20000000 in
/-- The box `B1 × B2 × B1`. -/
lemma box_0_1_0 (x y z : ℝ) (hx1 : (63/64:ℝ) ≤ x) (hx2 : x ≤ (73/64:ℝ))
    (hy1 : (121/64:ℝ) ≤ y) (hy2 : y ≤ (141/64:ℝ))
    (hz1 : (63/64:ℝ) ≤ z) (hz2 : z ≤ (73/64:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  rcases le_total y (131/64:ℝ) with hc | hc
  · rcases le_total x (17/16:ℝ) with hc | hc
    · rcases le_total y (63/32:ℝ) with hc | hc
      · rcases le_total z (17/16:ℝ) with hc | hc
        · rcases le_total x (131/128:ℝ) with hc | hc
          · exact ch_4 x y z (by linarith) (by linarith) (by linarith)
              (by linarith) (by linarith) (by linarith)
          · rcases le_total y (247/128:ℝ) with hc | hc
            · exact ch_5 x y z (by linarith) (by linarith) (by linarith)
                (by linarith) (by linarith) (by linarith)
            · rcases le_total z (131/128:ℝ) with hc | hc
              · exact ch_6 x y z (by linarith) (by linarith) (by linarith)
                  (by linarith) (by linarith) (by linarith)
              · rcases le_total x (267/256:ℝ) with hc | hc
                · exact ch_7 x y z (by linarith) (by linarith) (by linarith)
                    (by linarith) (by linarith) (by linarith)
                · exact ch_8 x y z (by linarith) (by linarith) (by linarith)
                    (by linarith) (by linarith) (by linarith)
        · exact ch_9 x y z (by linarith) (by linarith) (by linarith)
            (by linarith) (by linarith) (by linarith)
      · rcases le_total z (17/16:ℝ) with hc | hc
        · rcases le_total x (131/128:ℝ) with hc | hc
          · exact ch_10 x y z (by linarith) (by linarith) (by linarith)
              (by linarith) (by linarith) (by linarith)
          · rcases le_total y (257/128:ℝ) with hc | hc
            · rcases le_total z (131/128:ℝ) with hc | hc
              · exact ch_11 x y z (by linarith) (by linarith) (by linarith)
                  (by linarith) (by linarith) (by linarith)
              · rcases le_total x (267/256:ℝ) with hc | hc
                · rcases le_total y (509/256:ℝ) with hc | hc
                  · rcases le_total z (267/256:ℝ) with hc | hc
                    · rcases le_total x (529/512:ℝ) with hc | hc
                      · exact ch_12 x y z (by linarith) (by linarith) (by linarith)
                          (by linarith) (by linarith) (by linarith)
                      · rcases le_total y (1013/512:ℝ) with hc | hc
                        · exact ch_13 x y z (by linarith) (by linarith) (by linarith)
                            (by linarith) (by linarith) (by linarith)
                        · rcases le_total z (529/512:ℝ) with hc | hc
                          · exact ch_14 x y z (by linarith) (by linarith) (by linarith)
                              (by linarith) (by linarith) (by linarith)
                          · exact ch_15 x y z (by linarith) (by linarith) (by linarith)
                              (by linarith) (by linarith) (by linarith)
                    · rcases le_total x (529/512:ℝ) with hc | hc
                      · exact ch_16 x y z (by linarith) (by linarith) (by linarith)
                          (by linarith) (by linarith) (by linarith)
                      · rcases le_total y (1013/512:ℝ) with hc | hc
                        · rcases le_total z (539/512:ℝ) with hc | hc
                          · rcases le_total x (1063/1024:ℝ) with hc | hc
                            · exact ch_17 x y z (by linarith) (by linarith) (by linarith)
                                (by linarith) (by linarith) (by linarith)
                            · exact ch_18 x y z (by linarith) (by linarith) (by linarith)
                                (by linarith) (by linarith) (by linarith)
                          · exact ch_19 x y z (by linarith) (by linarith) (by linarith)
                              (by linarith) (by linarith) (by linarith)
                        · rcases le_total z (539/512:ℝ) with hc | hc
                          · rcases le_total x (1063/1024:ℝ) with hc | hc
                            · exact ch_20 x y z (by linarith) (by linarith) (by linarith)
                                (by linarith) (by linarith) (by linarith)
                            · rcases le_total y (2031/1024:ℝ) with hc | hc
                              · rcases le_total z (1073/1024:ℝ) with hc | hc
                                · rcases le_total x (2131/2048:ℝ) with hc | hc
                                  · exact ch_21 x y z (by linarith) (by linarith) (by linarith)
                                      (by linarith) (by linarith) (by linarith)
                                  · rcases le_total y (4057/2048:ℝ) with hc | hc
                                    · exact ch_22 x y z (by linarith) (by linarith) (by linarith)
                                        (by linarith) (by linarith) (by linarith)
                                    · exact ch_23 x y z (by linarith) (by linarith) (by linarith)
                                        (by linarith) (by linarith) (by linarith)
                                · exact ch_24 x y z (by linarith) (by linarith) (by linarith)
                                    (by linarith) (by linarith) (by linarith)
                              · rcases le_total z (1073/1024:ℝ) with hc | hc
                                · rcases le_total x (2131/2048:ℝ) with hc | hc
                                  · exact ch_25 x y z (by linarith) (by linarith) (by linarith)
                                      (by linarith) (by linarith) (by linarith)
                                  · rcases le_total y (4067/2048:ℝ) with hc | hc
                                    · exact ch_26 x y z (by linarith) (by linarith) (by linarith)
                                        (by linarith) (by linarith) (by linarith)
                                    · exact ch_27 x y z (by linarith) (by linarith) (by linarith)
                                        (by linarith) (by linarith) (by linarith)
                                · exact ch_28 x y z (by linarith) (by linarith) (by linarith)
                                    (by linarith) (by linarith) (by linarith)
                          · exact ch_29 x y z (by linarith) (by linarith) (by linarith)
                              (by linarith) (by linarith) (by linarith)
                  · rcases le_total z (267/256:ℝ) with hc | hc
                    · rcases le_total x (529/512:ℝ) with hc | hc
                      · exact ch_30 x y z (by linarith) (by linarith) (by linarith)
                          (by linarith) (by linarith) (by linarith)
                      · rcases le_total y (1023/512:ℝ) with hc | hc
                        · exact ch_31 x y z (by linarith) (by linarith) (by linarith)
                            (by linarith) (by linarith) (by linarith)
                        · exact ch_32 x y z (by linarith) (by linarith) (by linarith)
                            (by linarith) (by linarith) (by linarith)
                    · rcases le_total x (529/512:ℝ) with hc | hc
                      · exact ch_33 x y z (by linarith) (by linarith) (by linarith)
                          (by linarith) (by linarith) (by linarith)
                      · rcases le_total y (1023/512:ℝ) with hc | hc
                        · rcases le_total z (539/512:ℝ) with hc | hc
                          · rcases le_total x (1063/1024:ℝ) with hc | hc
                            · exact ch_34 x y z (by linarith) (by linarith) (by linarith)
                                (by linarith) (by linarith) (by linarith)
                            · rcases le_total y (2041/1024:ℝ) with hc | hc
                              · exact ch_35 x y z (by linarith) (by linarith) (by linarith)
                                  (by linarith) (by linarith) (by linarith)
                              · exact ch_36 x y z (by linarith) (by linarith) (by linarith)
                                  (by linarith) (by linarith) (by linarith)
                          · exact ch_37 x y z (by linarith) (by linarith) (by linarith)
                              (by linarith) (by linarith) (by linarith)
                        · exact ch_38 x y z (by linarith) (by linarith) (by linarith)
                            (by linarith) (by linarith) (by linarith)
                · rcases le_total y (509/256:ℝ) with hc | hc
                  · rcases le_total z (267/256:ℝ) with hc | hc
                    · rcases le_total x (539/512:ℝ) with hc | hc
                      · rcases le_total y (1013/512:ℝ) with hc | hc
                        · rcases le_total z (529/512:ℝ) with hc | hc
                          · exact ch_39 x y z (by linarith) (by linarith) (by linarith)
                              (by linarith) (by linarith) (by linarith)
                          · rcases le_total x (1073/1024:ℝ) with hc | hc
                            · exact ch_40 x y z (by linarith) (by linarith) (by linarith)
                                (by linarith) (by linarith) (by linarith)
                            · exact ch_41 x y z (by linarith) (by linarith) (by linarith)
                                (by linarith) (by linarith) (by linarith)
                        · rcases le_total z (529/512:ℝ) with hc | hc
                          · exact ch_42 x y z (by linarith) (by linarith) (by linarith)
                              (by linarith) (by linarith) (by linarith)
                          · rcases le_total x (1073/1024:ℝ) with hc | hc
                            · rcases le_total y (2031/1024:ℝ) with hc | hc
                              · rcases le_total z (1063/1024:ℝ) with hc | hc
                                · exact ch_43 x y z (by linarith) (by linarith) (by linarith)
                                    (by linarith) (by linarith) (by linarith)
                                · rcases le_total x (2141/2048:ℝ) with hc | hc
                                  · exact ch_44 x y z (by linarith) (by linarith) (by linarith)
                                      (by linarith) (by linarith) (by linarith)
                                  · exact ch_45 x y z (by linarith) (by linarith) (by linarith)
                                      (by linarith) (by linarith) (by linarith)
                              · rcases le_total z (1063/1024:ℝ) with hc | hc
                                · exact ch_46 x y z (by linarith) (by linarith) (by linarith)
                                    (by linarith) (by linarith) (by linarith)
                                · rcases le_total x (2141/2048:ℝ) with hc | hc
                                  · exact ch_47 x y z (by linarith) (by linarith) (by linarith)
                                      (by linarith) (by linarith) (by linarith)
                                  · rcases le_total y (4067/2048:ℝ) with hc | hc
                                    · exact ch_48 x y z (by linarith) (by linarith) (by linarith)
                                        (by linarith) (by linarith) (by linarith)
                                    · exact ch_49 x y z (by linarith) (by linarith) (by linarith)
                                        (by linarith) (by linarith) (by linarith)
                            · rcases le_total y (2031/1024:ℝ) with hc | hc
                              · rcases le_total z (1063/1024:ℝ) with hc | hc
                                · exact ch_50 x y z (by linarith) (by linarith) (by linarith)
                                    (by linarith) (by linarith) (by linarith)
                                · rcases le_total x (2151/2048:ℝ) with hc | hc
                                  · exact ch_51 x y z (by linarith) (by linarith) (by linarith)
                                      (by linarith) (by linarith) (by linarith)
                                  · exact ch_52 x y z (by linarith) (by linarith) (by linarith)
                                      (by linarith) (by linarith) (by linarith)
                              · rcases le_total z (1063/1024:ℝ) with hc | hc
                                · exact ch_53 x y z (by linarith) (by linarith) (by linarith)
                                    (by linarith) (by linarith) (by linarith)
                                · exact ch_54 x y z (by linarith) (by linarith) (by linarith)
                                    (by linarith) (by linarith) (by linarith)
                      · exact ch_55 x y z (by linarith) (by linarith) (by linarith)
                          (by linarith) (by linarith) (by linarith)
                    · rcases le_total x (539/512:ℝ) with hc | hc
                      · rcases le_total y (1013/512:ℝ) with hc | hc
                        · rcases le_total z (539/512:ℝ) with hc | hc
                          · rcases le_total x (1073/1024:ℝ) with hc | hc
                            · rcases le_total y (2021/1024:ℝ) with hc | hc
                              · exact ch_56 x y z (by linarith) (by linarith) (by linarith)
                                  (by linarith) (by linarith) (by linarith)
                              · rcases le_total z (1073/1024:ℝ) with hc | hc
                                · rcases le_total x (2141/2048:ℝ) with hc | hc
                                  · rcases le_total y (4047/2048:ℝ) with hc | hc
                                    · exact ch_57 x y z (by linarith) (by linarith) (by linarith)
                                        (by linarith) (by linarith) (by linarith)
                                    · exact ch_58 x y z (by linarith) (by linarith) (by linarith)
                                        (by linarith) (by linarith) (by linarith)
                                  · rcases le_total y (4047/2048:ℝ) with hc | hc
                                    · exact ch_59 x y z (by linarith) (by linarith) (by linarith)
                                        (by linarith) (by linarith) (by linarith)
                                    · rcases le_total z (2141/2048:ℝ) with hc | hc
                                      · exact ch_60 x y z (by linarith) (by linarith) (by linarith)
                                          (by linarith) (by linarith) (by linarith)
                                      · rcases le_total x (4287/4096:ℝ) with hc | hc
                                        · exact ch_61 x y z (by linarith) (by linarith) (by linarith)
                                            (by linarith) (by linarith) (by linarith)
                                        · exact ch_62 x y z (by linarith) (by linarith) (by linarith)
                                            (by linarith) (by linarith) (by linarith)
                                · rcases le_total x (2141/2048:ℝ) with hc | hc
                                  · rcases le_total y (4047/2048:ℝ) with hc | hc
                                    · exact ch_63 x y z (by linarith) (by linarith) (by linarith)
                                        (by linarith) (by linarith) (by linarith)
                                    · exact ch_64 x y z (by linarith) (by linarith) (by linarith)
                                        (by linarith) (by linarith) (by linarith)
                                  · rcases le_total y (4047/2048:ℝ) with hc | hc
                                    · exact ch_65 x y z (by linarith) (by linarith) (by linarith)
                                        (by linarith) (by linarith) (by linarith)
                                    · rcases le_total z (2151/2048:ℝ) with hc | hc
                                      · rcases le_total x (4287/4096:ℝ) with hc | hc
                                        · exact ch_66 x y z (by linarith) (by linarith) (by linarith)
                                            (by linarith) (by linarith) (by linarith)
                                        · exact ch_67 x y z (by linarith) (by linarith) (by linarith)
                                            (by linarith) (by linarith) (by linarith)
                                      · exact ch_68 x y z (by linarith) (by linarith) (by linarith)
                                          (by linarith) (by linarith) (by linarith)
                            · rcases le_total y (2021/1024:ℝ) with hc | hc
                              · exact ch_69 x y z (by linarith) (by linarith) (by linarith)
                                  (by linarith) (by linarith) (by linarith)
                              · rcases le_total z (1073/1024:ℝ) with hc | hc
                                · rcases le_total x (2151/2048:ℝ) with hc | hc
                                  · rcases le_total y (4047/2048:ℝ) with hc | hc
                                    · exact ch_70 x y z (by linarith) (by linarith) (by linarith)
                                        (by linarith) (by linarith) (by linarith)
                                    · rcases le_total z (2141/2048:ℝ) with hc | hc
                                      · exact ch_71 x y z (by linarith) (by linarith) (by linarith)
                                          (by linarith) (by linarith) (by linarith)
                                      · rcases le_total x (4297/4096:ℝ) with hc | hc
                                        · exact ch_72 x y z (by linarith) (by linarith) (by linarith)
                                            (by linarith) (by linarith) (by linarith)
                                        · exact ch_73 x y z (by linarith) (by linarith) (by linarith)
                                            (by linarith) (by linarith) (by linarith)
                                  · exact ch_74 x y z (by linarith) (by linarith) (by linarith)
                                      (by linarith) (by linarith) (by linarith)
                                · rcases le_total x (2151/2048:ℝ) with hc | hc
                                  · rcases le_total y (4047/2048:ℝ) with hc | hc
                                    · exact ch_75 x y z (by linarith) (by linarith) (by linarith)
                                        (by linarith) (by linarith) (by linarith)
                                    · rcases le_total z (2151/2048:ℝ) with hc | hc
                                      · exact ch_76 x y z (by linarith) (by linarith) (by linarith)
                                          (by linarith) (by linarith) (by linarith)
                                      · exact ch_77 x y z (by linarith) (by linarith) (by linarith)
                                          (by linarith) (by linarith) (by linarith)
                                  · exact ch_78 x y z (by linarith) (by linarith) (by linarith)
                                      (by linarith) (by linarith) (by linarith)
                          · exact ch_79 x y z (by linarith) (by linarith) (by linarith)
                              (by linarith) (by linarith) (by linarith)
                        · rcases le_total z (539/512:ℝ) with hc | hc
                          · rcases le_total x (1073/1024:ℝ) with hc | hc
                            · rcases le_total y (2031/1024:ℝ) with hc | hc
                              · rcases le_total z (1073/1024:ℝ) with hc | hc
                                · rcases le_total x (2141/2048:ℝ) with hc | hc
                                  · rcases le_total y (4057/2048:ℝ) with hc | hc
                                    · rcases le_total z (2141/2048:ℝ) with hc | hc
                                      · exact ch_80 x y z (by linarith) (by linarith) (by linarith)
                                          (by linarith) (by linarith) (by linarith)
                                      · rcases le_total x (4277/4096:ℝ) with hc | hc
                                        · exact ch_81 x y z (by linarith) (by linarith) (by linarith)
                                            (by linarith) (by linarith) (by linarith)
                                        · exact ch_82 x y z (by linarith) (by linarith) (by linarith)
                                            (by linarith) (by linarith) (by linarith)
                                    · rcases le_total z (2141/2048:ℝ) with hc | hc
                                      · rcases le_total x (4277/4096:ℝ) with hc | hc
                                        · exact ch_83 x y z (by linarith) (by linarith) (by linarith)
                                            (by linarith) (by linarith) (by linarith)
                                        · exact ch_84 x y z (by linarith) (by linarith) (by linarith)
                                            (by linarith) (by linarith) (by linarith)
                                      · rcases le_total x (4277/4096:ℝ) with hc | hc
                                        · exact ch_85 x y z (by linarith) (by linarith) (by linarith)
                                            (by linarith) (by linarith) (by linarith)
                                        · rcases le_total y (8119/4096:ℝ) with hc | hc
                                          · exact ch_86 x y z (by linarith) (by linarith) (by linarith)
                                              (by linarith) (by linarith) (by linarith)
                                          · exact ch_87 x y z (by linarith) (by linarith) (by linarith)
                                              (by linarith) (by linarith) (by linarith)
                                  · rcases le_total y (4057/2048:ℝ) with hc | hc
                                    · rcases le_total z (2141/2048:ℝ) with hc | hc
                                      · rcases le_total x (4287/4096:ℝ) with hc | hc
                                        · exact ch_88 x y z (by linarith) (by linarith) (by linarith)
                                            (by linarith) (by linarith) (by linarith)
                                        · exact ch_89 x y z (by linarith) (by linarith) (by linarith)
                                            (by linarith) (by linarith) (by linarith)
                                      · rcases le_total x (4287/4096:ℝ) with hc | hc
                                        · rcases le_total y (8109/4096:ℝ) with hc | hc
                                          · exact ch_90 x y z (by linarith) (by linarith) (by linarith)
                                              (by linarith) (by linarith) (by linarith)
                                          · rcases le_total z (4287/4096:ℝ) with hc | hc
                                            · exact ch_91 x y z (by linarith) (by linarith) (by linarith)
                                                (by linarith) (by linarith) (by linarith)
                                            · exact ch_92 x y z (by linarith) (by linarith) (by linarith)
                                                (by linarith) (by linarith) (by linarith)
                                        · rcases le_total y (8109/4096:ℝ) with hc | hc
                                          · exact ch_93 x y z (by linarith) (by linarith) (by linarith)
                                              (by linarith) (by linarith) (by linarith)
                                          · rcases le_total z (4287/4096:ℝ) with hc | hc
                                            · exact ch_94 x y z (by linarith) (by linarith) (by linarith)
                                                (by linarith) (by linarith) (by linarith)
                                            · exact ch_95 x y z (by linarith) (by linarith) (by linarith)
                                                (by linarith) (by linarith) (by linarith)
                                    · rcases le_total z (2141/2048:ℝ) with hc | hc
                                      · rcases le_total x (4287/4096:ℝ) with hc | hc
                                        · rcases le_total y (8119/4096:ℝ) with hc | hc
                                          · exact ch_96 x y z (by linarith) (by linarith) (by linarith)
                                              (by linarith) (by linarith) (by linarith)
                                          · exact ch_97 x y z (by linarith) (by linarith) (by linarith)
                                              (by linarith) (by linarith) (by linarith)
                                        · rcases le_total y (8119/4096:ℝ) with hc | hc
                                          · exact ch_98 x y z (by linarith) (by linarith) (by linarith)
                                              (by linarith) (by linarith) (by linarith)
                                          · exact ch_99 x y z (by linarith) (by linarith) (by linarith)
                                              (by linarith) (by linarith) (by linarith)
                                      · rcases le_total x (4287/4096:ℝ) with hc | hc
                                        · rcases le_total y (8119/4096:ℝ) with hc | hc
                                          · rcases le_total z (4287/4096:ℝ) with hc | hc
                                            · exact ch_100 x y z (by linarith) (by linarith) (by linarith)
                                                (by linarith) (by linarith) (by linarith)
                                            · exact ch_101 x y z (by linarith) (by linarith) (by linarith)
                                                (by linarith) (by linarith) (by linarith)
                                          · rcases le_total z (4287/4096:ℝ) with hc | hc
                                            · exact ch_102 x y z (by linarith) (by linarith) (by linarith)
                                                (by linarith) (by linarith) (by linarith)
                                            · exact ch_103 x y z (by linarith) (by linarith) (by linarith)
                                                (by linarith) (by linarith) (by linarith)
                                        · rcases le_total y (8119/4096:ℝ) with hc | hc
                                          · rcases le_total z (4287/4096:ℝ) with hc | hc
                                            · exact ch_104 x y z (by linarith) (by linarith) (by linarith)
                                                (by linarith) (by linarith) (by linarith)
                                            · exact ch_105 x y z (by linarith) (by linarith) (by linarith)
                                                (by linarith) (by linarith) (by linarith)
                                          · exact ch_106 x y z (by linarith) (by linarith) (by linarith)
                                              (by linarith) (by linarith) (by linarith)
                                · rcases le_total x (2141/2048:ℝ) with hc | hc
                                  · rcases le_total y (4057/2048:ℝ) with hc | hc
                                    · rcases le_total z (2151/2048:ℝ) with hc | hc
                                      · exact ch_107 x y z (by linarith) (by linarith) (by linarith)
                                          (by linarith) (by linarith) (by linarith)
                                      · exact ch_108 x y z (by linarith) (by linarith) (by linarith)
                                          (by linarith) (by linarith) (by linarith)
                                    · rcases le_total z (2151/2048:ℝ) with hc | hc
                                      · rcases le_total x (4277/4096:ℝ) with hc | hc
                                        · exact ch_109 x y z (by linarith) (by linarith) (by linarith)
                                            (by linarith) (by linarith) (by linarith)
                                        · exact ch_110 x y z (by linarith) (by linarith) (by linarith)
                                            (by linarith) (by linarith) (by linarith)
                                      · exact ch_111 x y z (by linarith) (by linarith) (by linarith)
                                          (by linarith) (by linarith) (by linarith)
                                  · rcases le_total y (4057/2048:ℝ) with hc | hc
                                    · rcases le_total z (2151/2048:ℝ) with hc | hc
                                      · rcases le_total x (4287/4096:ℝ) with hc | hc
                                        · rcases le_total y (8109/4096:ℝ) with hc | hc
                                          · exact ch_112 x y z (by linarith) (by linarith) (by linarith)
                                              (by linarith) (by linarith) (by linarith)
                                          · exact ch_113 x y z (by linarith) (by linarith) (by linarith)
                                              (by linarith) (by linarith) (by linarith)
                                        · rcases le_total y (8109/4096:ℝ) with hc | hc
                                          · exact ch_114 x y z (by linarith) (by linarith) (by linarith)
                                              (by linarith) (by linarith) (by linarith)
                                          · exact ch_115 x y z (by linarith) (by linarith) (by linarith)
                                              (by linarith) (by linarith) (by linarith)
                                      · exact ch_116 x y z (by linarith) (by linarith) (by linarith)
                                          (by linarith) (by linarith) (by linarith)
                                    · rcases le_total z (2151/2048:ℝ) with hc | hc
                                      · rcases le_total x (4287/4096:ℝ) with hc | hc
                                        · exact ch_117 x y z (by linarith) (by linarith) (by linarith)
                                            (by linarith) (by linarith) (by linarith)
                                        · exact ch_118 x y z (by linarith) (by linarith) (by linarith)
                                            (by linarith) (by linarith) (by linarith)
                                      · exact ch_119 x y z (by linarith) (by linarith) (by linarith)
                                          (by linarith) (by linarith) (by linarith)
                              · rcases le_total z (1073/1024:ℝ) with hc | hc
                                · rcases le_total x (2141/2048:ℝ) with hc | hc
                                  · rcases le_total y (4067/2048:ℝ) with hc | hc
                                    · rcases le_total z (2141/2048:ℝ) with hc | hc
                                      · rcases le_total x (4277/4096:ℝ) with hc | hc
                                        · exact ch_120 x y z (by linarith) (by linarith) (by linarith)
                                            (by linarith) (by linarith) (by linarith)
                                        · exact ch_121 x y z (by linarith) (by linarith) (by linarith)
                                            (by linarith) (by linarith) (by linarith)
                                      · rcases le_total x (4277/4096:ℝ) with hc | hc
                                        · exact ch_122 x y z (by linarith) (by linarith) (by linarith)
                                            (by linarith) (by linarith) (by linarith)
                                        · exact ch_123 x y z (by linarith) (by linarith) (by linarith)
                                            (by linarith) (by linarith) (by linarith)
                                    · rcases le_total z (2141/2048:ℝ) with hc | hc
                                      · exact ch_124 x y z (by linarith) (by linarith) (by linarith)
                                          (by linarith) (by linarith) (by linarith)
                                      · exact ch_125 x y z (by linarith) (by linarith) (by linarith)
                                          (by linarith) (by linarith) (by linarith)
                                  · rcases le_total y (4067/2048:ℝ) with hc | hc
                                    · rcases le_total z (2141/2048:ℝ) with hc | hc
                                      · rcases le_total x (4287/4096:ℝ) with hc | hc
                                        · exact ch_126 x y z (by linarith) (by linarith) (by linarith)
                                            (by linarith) (by linarith) (by linarith)
                                        · exact ch_127 x y z (by linarith) (by linarith) (by linarith)
                                            (by linarith) (by linarith) (by linarith)
                                      · rcases le_total x (4287/4096:ℝ) with hc | hc
                                        · rcases le_total y (8129/4096:ℝ) with hc | hc
                                          · exact ch_128 x y z (by linarith) (by linarith) (by linarith)
                                              (by linarith) (by linarith) (by linarith)
                                          · exact ch_129 x y z (by linarith) (by linarith) (by linarith)
                                              (by linarith) (by linarith) (by linarith)
                                        · exact ch_130 x y z (by linarith) (by linarith) (by linarith)
                                            (by linarith) (by linarith) (by linarith)
                                    · rcases le_total z (2141/2048:ℝ) with hc | hc
                                      · exact ch_131 x y z (by linarith) (by linarith) (by linarith)
                                          (by linarith) (by linarith) (by linarith)
                                      · exact ch_132 x y z (by linarith) (by linarith) (by linarith)
                                          (by linarith) (by linarith) (by linarith)
                                · rcases le_total x (2141/2048:ℝ) with hc | hc
                                  · rcases le_total y (4067/2048:ℝ) with hc | hc
                                    · exact ch_133 x y z (by linarith) (by linarith) (by linarith)
                                        (by linarith) (by linarith) (by linarith)
                                    · exact ch_134 x y z (by linarith) (by linarith) (by linarith)
                                        (by linarith) (by linarith) (by linarith)
                                  · rcases le_total y (4067/2048:ℝ) with hc | hc
                                    · rcases le_total z (2151/2048:ℝ) with hc | hc
                                      · exact ch_135 x y z (by linarith) (by linarith) (by linarith)
                                          (by linarith) (by linarith) (by linarith)
                                      · exact ch_136 x y z (by linarith) (by linarith) (by linarith)
                                          (by linarith) (by linarith) (by linarith)
                                    · exact ch_137 x y z (by linarith) (by linarith) (by linarith)
                                        (by linarith) (by linarith) (by linarith)
                            · rcases le_total y (2031/1024:ℝ) with hc | hc
                              · rcases le_total z (1073/1024:ℝ) with hc | hc
                                · rcases le_total x (2151/2048:ℝ) with hc | hc
                                  · rcases le_total y (4057/2048:ℝ) with hc | hc
                                    · rcases le_total z (2141/2048:ℝ) with hc | hc
                                      · rcases le_total x (4297/4096:ℝ) with hc | hc
                                        · exact ch_138 x y z (by linarith) (by linarith) (by linarith)
                                            (by linarith) (by linarith) (by linarith)
                                        · exact ch_139 x y z (by linarith) (by linarith) (by linarith)
                                            (by linarith) (by linarith) (by linarith)
                                      · rcases le_total x (4297/4096:ℝ) with hc | hc
                                        · rcases le_total y (8109/4096:ℝ) with hc | hc
                                          · exact ch_140 x y z (by linarith) (by linarith) (by linarith)
                                              (by linarith) (by linarith) (by linarith)
                                          · exact ch_141 x y z (by linarith) (by linarith) (by linarith)
                                              (by linarith) (by linarith) (by linarith)
                                        · exact ch_142 x y z (by linarith) (by linarith) (by linarith)
                                            (by linarith) (by linarith) (by linarith)
                                    · rcases le_total z (2141/2048:ℝ) with hc | hc
                                      · rcases le_total x (4297/4096:ℝ) with hc | hc
                                        · exact ch_143 x y z (by linarith) (by linarith) (by linarith)
                                            (by linarith) (by linarith) (by linarith)
                                        · exact ch_144 x y z (by linarith) (by linarith) (by linarith)
                                            (by linarith) (by linarith) (by linarith)
                                      · rcases le_total x (4297/4096:ℝ) with hc | hc
                                        · rcases le_total y (8119/4096:ℝ) with hc | hc
                                          · exact ch_145 x y z (by linarith) (by linarith) (by linarith)
                                              (by linarith) (by linarith) (by linarith)
                                          · exact ch_146 x y z (by linarith) (by linarith) (by linarith)
                                              (by linarith) (by linarith) (by linarith)
                                        · exact ch_147 x y z (by linarith) (by linarith) (by linarith)
                                            (by linarith) (by linarith) (by linarith)
                                  · rcases le_total y (4057/2048:ℝ) with hc | hc
                                    · exact ch_148 x y z (by linarith) (by linarith) (by linarith)
                                        (by linarith) (by linarith) (by linarith)
                                    · exact ch_149 x y z (by linarith) (by linarith) (by linarith)
                                        (by linarith) (by linarith) (by linarith)
                                · rcases le_total x (2151/2048:ℝ) with hc | hc
                                  · rcases le_total y (4057/2048:ℝ) with hc | hc
                                    · rcases le_total z (2151/2048:ℝ) with hc | hc
                                      · rcases le_total x (4297/4096:ℝ) with hc | hc
                                        · exact ch_150 x y z (by linarith) (by linarith) (by linarith)
                                            (by linarith) (by linarith) (by linarith)
                                        · exact ch_151 x y z (by linarith) (by linarith) (by linarith)
                                            (by linarith) (by linarith) (by linarith)
                                      · exact ch_152 x y z (by linarith) (by linarith) (by linarith)
                                          (by linarith) (by linarith) (by linarith)
                                    · rcases le_total z (2151/2048:ℝ) with hc | hc
                                      · exact ch_153 x y z (by linarith) (by linarith) (by linarith)
                                          (by linarith) (by linarith) (by linarith)
                                      · exact ch_154 x y z (by linarith) (by linarith) (by linarith)
                                          (by linarith) (by linarith) (by linarith)
                                  · exact ch_155 x y z (by linarith) (by linarith) (by linarith)
                                      (by linarith) (by linarith) (by linarith)
                              · rcases le_total z (1073/1024:ℝ) with hc | hc
                                · rcases le_total x (2151/2048:ℝ) with hc | hc
                                  · rcases le_total y (4067/2048:ℝ) with hc | hc
                                    · rcases le_total z (2141/2048:ℝ) with hc | hc
                                      · exact ch_156 x y z (by linarith) (by linarith) (by linarith)
                                          (by linarith) (by linarith) (by linarith)
                                      · exact ch_157 x y z (by linarith) (by linarith) (by linarith)
                                          (by linarith) (by linarith) (by linarith)
                                    · exact ch_158 x y z (by linarith) (by linarith) (by linarith)
                                        (by linarith) (by linarith) (by linarith)
                                  · exact ch_159 x y z (by linarith) (by linarith) (by linarith)
                                      (by linarith) (by linarith) (by linarith)
                                · exact ch_160 x y z (by linarith) (by linarith) (by linarith)
                                    (by linarith) (by linarith) (by linarith)
                          · exact ch_161 x y z (by linarith) (by linarith) (by linarith)
                              (by linarith) (by linarith) (by linarith)
                      · rcases le_total y (1013/512:ℝ) with hc | hc
                        · rcases le_total z (539/512:ℝ) with hc | hc
                          · exact ch_162 x y z (by linarith) (by linarith) (by linarith)
                              (by linarith) (by linarith) (by linarith)
                          · exact ch_163 x y z (by linarith) (by linarith) (by linarith)
                              (by linarith) (by linarith) (by linarith)
                        · rcases le_total z (539/512:ℝ) with hc | hc
                          · exact ch_164 x y z (by linarith) (by linarith) (by linarith)
                              (by linarith) (by linarith) (by linarith)
                          · exact ch_165 x y z (by linarith) (by linarith) (by linarith)
                              (by linarith) (by linarith) (by linarith)
                  · rcases le_total z (267/256:ℝ) with hc | hc
                    · rcases le_total x (539/512:ℝ) with hc | hc
                      · rcases le_total y (1023/512:ℝ) with hc | hc
                        · rcases le_total z (529/512:ℝ) with hc | hc
                          · exact ch_166 x y z (by linarith) (by linarith) (by linarith)
                              (by linarith) (by linarith) (by linarith)
                          · rcases le_total x (1073/1024:ℝ) with hc | hc
                            · rcases le_total y (2041/1024:ℝ) with hc | hc
                              · exact ch_167 x y z (by linarith) (by linarith) (by linarith)
                                  (by linarith) (by linarith) (by linarith)
                              · exact ch_168 x y z (by linarith) (by linarith) (by linarith)
                                  (by linarith) (by linarith) (by linarith)
                            · exact ch_169 x y z (by linarith) (by linarith) (by linarith)
                                (by linarith) (by linarith) (by linarith)
                        · exact ch_170 x y z (by linarith) (by linarith) (by linarith)
                            (by linarith) (by linarith) (by linarith)
                      · exact ch_171 x y z (by linarith) (by linarith) (by linarith)
                          (by linarith) (by linarith) (by linarith)
                    · rcases le_total x (539/512:ℝ) with hc | hc
                      · rcases le_total y (1023/512:ℝ) with hc | hc
                        · rcases le_total z (539/512:ℝ) with hc | hc
                          · rcases le_total x (1073/1024:ℝ) with hc | hc
                            · rcases le_total y (2041/1024:ℝ) with hc | hc
                              · rcases le_total z (1073/1024:ℝ) with hc | hc
                                · rcases le_total x (2141/2048:ℝ) with hc | hc
                                  · exact ch_172 x y z (by linarith) (by linarith) (by linarith)
                                      (by linarith) (by linarith) (by linarith)
                                  · exact ch_173 x y z (by linarith) (by linarith) (by linarith)
                                      (by linarith) (by linarith) (by linarith)
                                · exact ch_174 x y z (by linarith) (by linarith) (by linarith)
                                    (by linarith) (by linarith) (by linarith)
                              · exact ch_175 x y z (by linarith) (by linarith) (by linarith)
                                  (by linarith) (by linarith) (by linarith)
                            · exact ch_176 x y z (by linarith) (by linarith) (by linarith)
                                (by linarith) (by linarith) (by linarith)
                          · exact ch_177 x y z (by linarith) (by linarith) (by linarith)
                              (by linarith) (by linarith) (by linarith)
                        · exact ch_178 x y z (by linarith) (by linarith) (by linarith)
                            (by linarith) (by linarith) (by linarith)
                      · exact ch_179 x y z (by linarith) (by linarith) (by linarith)
                          (by linarith) (by linarith) (by linarith)
            · exact ch_180 x y z (by linarith) (by linarith) (by linarith)
                (by linarith) (by linarith) (by linarith)
        · exact ch_181 x y z (by linarith) (by linarith) (by linarith)
            (by linarith) (by linarith) (by linarith)
    · exact ch_182 x y z (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith)
  · exact ch_183 x y z (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith) (by linarith)

set_option maxHeartbeats 20000000 in
/-- The box `B1 × B2 × B2`. -/
lemma box_0_1_1 (x y z : ℝ) (hx1 : (63/64:ℝ) ≤ x) (hx2 : x ≤ (73/64:ℝ))
    (hy1 : (121/64:ℝ) ≤ y) (hy2 : y ≤ (141/64:ℝ))
    (hz1 : (121/64:ℝ) ≤ z) (hz2 : z ≤ (141/64:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  rcases le_total y (131/64:ℝ) with hc | hc
  · rcases le_total z (131/64:ℝ) with hc | hc
    · rcases le_total x (17/16:ℝ) with hc | hc
      · rcases le_total y (63/32:ℝ) with hc | hc
        · exact ch_184 x y z (by linarith) (by linarith) (by linarith)
            (by linarith) (by linarith) (by linarith)
        · rcases le_total z (63/32:ℝ) with hc | hc
          · exact ch_185 x y z (by linarith) (by linarith) (by linarith)
              (by linarith) (by linarith) (by linarith)
          · rcases le_total x (131/128:ℝ) with hc | hc
            · exact ch_186 x y z (by linarith) (by linarith) (by linarith)
                (by linarith) (by linarith) (by linarith)
            · rcases le_total y (257/128:ℝ) with hc | hc
              · rcases le_total z (257/128:ℝ) with hc | hc
                · exact ch_187 x y z (by linarith) (by linarith) (by linarith)
                    (by linarith) (by linarith) (by linarith)
                · rcases le_total x (267/256:ℝ) with hc | hc
                  · exact ch_188 x y z (by linarith) (by linarith) (by linarith)
                      (by linarith) (by linarith) (by linarith)
                  · rcases le_total y (509/256:ℝ) with hc | hc
                    · exact ch_189 x y z (by linarith) (by linarith) (by linarith)
                        (by linarith) (by linarith) (by linarith)
                    · rcases le_total z (519/256:ℝ) with hc | hc
                      · exact ch_190 x y z (by linarith) (by linarith) (by linarith)
                          (by linarith) (by linarith) (by linarith)
                      · exact ch_191 x y z (by linarith) (by linarith) (by linarith)
                          (by linarith) (by linarith) (by linarith)
              · exact ch_192 x y z (by linarith) (by linarith) (by linarith)
                  (by linarith) (by linarith) (by linarith)
      · exact ch_193 x y z (by linarith) (by linarith) (by linarith)
          (by linarith) (by linarith) (by linarith)
    · exact ch_194 x y z (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith)
  · exact ch_195 x y z (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith) (by linarith)

set_option maxHeartbeats 20000000 in
/-- The box `B1 × B2 × B3`. -/
lemma box_0_1_2 (x y z : ℝ) (hx1 : (63/64:ℝ) ≤ x) (hx2 : x ≤ (73/64:ℝ))
    (hy1 : (121/64:ℝ) ≤ y) (hy2 : y ≤ (141/64:ℝ))
    (hz1 : (179/64:ℝ) ≤ z) (hz2 : z ≤ (105/32:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  exact ch_196 x y z (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith)

set_option maxHeartbeats 20000000 in
/-- The box `B1 × B3 × B1`. -/
lemma box_0_2_0 (x y z : ℝ) (hx1 : (63/64:ℝ) ≤ x) (hx2 : x ≤ (73/64:ℝ))
    (hy1 : (179/64:ℝ) ≤ y) (hy2 : y ≤ (105/32:ℝ))
    (hz1 : (63/64:ℝ) ≤ z) (hz2 : z ≤ (73/64:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  rcases le_total y (389/128:ℝ) with hc | hc
  · rcases le_total y (747/256:ℝ) with hc | hc
    · exact ch_197 x y z (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith)
    · rcases le_total x (17/16:ℝ) with hc | hc
      · rcases le_total z (17/16:ℝ) with hc | hc
        · rcases le_total y (1525/512:ℝ) with hc | hc
          · rcases le_total x (131/128:ℝ) with hc | hc
            · exact ch_198 x y z (by linarith) (by linarith) (by linarith)
                (by linarith) (by linarith) (by linarith)
            · rcases le_total z (131/128:ℝ) with hc | hc
              · exact ch_199 x y z (by linarith) (by linarith) (by linarith)
                  (by linarith) (by linarith) (by linarith)
              · rcases le_total y (3019/1024:ℝ) with hc | hc
                · exact ch_200 x y z (by linarith) (by linarith) (by linarith)
                    (by linarith) (by linarith) (by linarith)
                · rcases le_total x (267/256:ℝ) with hc | hc
                  · exact ch_201 x y z (by linarith) (by linarith) (by linarith)
                      (by linarith) (by linarith) (by linarith)
                  · rcases le_total z (267/256:ℝ) with hc | hc
                    · exact ch_202 x y z (by linarith) (by linarith) (by linarith)
                        (by linarith) (by linarith) (by linarith)
                    · rcases le_total y (6069/2048:ℝ) with hc | hc
                      · exact ch_203 x y z (by linarith) (by linarith) (by linarith)
                          (by linarith) (by linarith) (by linarith)
                      · exact ch_204 x y z (by linarith) (by linarith) (by linarith)
                          (by linarith) (by linarith) (by linarith)
          · exact ch_205 x y z (by linarith) (by linarith) (by linarith)
              (by linarith) (by linarith) (by linarith)
        · exact ch_206 x y z (by linarith) (by linarith) (by linarith)
            (by linarith) (by linarith) (by linarith)
      · exact ch_207 x y z (by linarith) (by linarith) (by linarith)
          (by linarith) (by linarith) (by linarith)
  · exact ch_208 x y z (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith) (by linarith)

set_option maxHeartbeats 20000000 in
/-- The box `B1 × B3 × B2`. -/
lemma box_0_2_1 (x y z : ℝ) (hx1 : (63/64:ℝ) ≤ x) (hx2 : x ≤ (73/64:ℝ))
    (hy1 : (179/64:ℝ) ≤ y) (hy2 : y ≤ (105/32:ℝ))
    (hz1 : (121/64:ℝ) ≤ z) (hz2 : z ≤ (141/64:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  exact ch_209 x y z (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith)

set_option maxHeartbeats 20000000 in
/-- The box `B1 × B4 × B1`. -/
lemma box_0_3_0 (x y z : ℝ) (hx1 : (63/64:ℝ) ≤ x) (hx2 : x ≤ (73/64:ℝ))
    (hy1 : (237/64:ℝ) ≤ y) (hy2 : y ≤ (233/40:ℝ))
    (hz1 : (63/64:ℝ) ≤ z) (hz2 : z ≤ (73/64:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  exact ch_210 x y z (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith)

set_option maxHeartbeats 20000000 in
/-- The box `B2 × B1 × B2`. -/
lemma box_1_0_1 (x y z : ℝ) (hx1 : (121/64:ℝ) ≤ x) (hx2 : x ≤ (141/64:ℝ))
    (hy1 : (63/64:ℝ) ≤ y) (hy2 : y ≤ (73/64:ℝ))
    (hz1 : (121/64:ℝ) ≤ z) (hz2 : z ≤ (141/64:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  rcases le_total x (131/64:ℝ) with hc | hc
  · rcases le_total z (131/64:ℝ) with hc | hc
    · rcases le_total x (63/32:ℝ) with hc | hc
      · exact ch_211 x y z (by linarith) (by linarith) (by linarith)
          (by linarith) (by linarith) (by linarith)
      · rcases le_total y (17/16:ℝ) with hc | hc
        · rcases le_total z (63/32:ℝ) with hc | hc
          · exact ch_212 x y z (by linarith) (by linarith) (by linarith)
              (by linarith) (by linarith) (by linarith)
          · rcases le_total x (257/128:ℝ) with hc | hc
            · exact ch_213 x y z (by linarith) (by linarith) (by linarith)
                (by linarith) (by linarith) (by linarith)
            · exact ch_214 x y z (by linarith) (by linarith) (by linarith)
                (by linarith) (by linarith) (by linarith)
        · exact ch_215 x y z (by linarith) (by linarith) (by linarith)
            (by linarith) (by linarith) (by linarith)
    · exact ch_216 x y z (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith)
  · exact ch_217 x y z (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith) (by linarith)

set_option maxHeartbeats 20000000 in
/-- The box `B2 × B1 × B3`. -/
lemma box_1_0_2 (x y z : ℝ) (hx1 : (121/64:ℝ) ≤ x) (hx2 : x ≤ (141/64:ℝ))
    (hy1 : (63/64:ℝ) ≤ y) (hy2 : y ≤ (73/64:ℝ))
    (hz1 : (179/64:ℝ) ≤ z) (hz2 : z ≤ (105/32:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  exact ch_218 x y z (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith)

set_option maxHeartbeats 20000000 in
/-- The box `B2 × B2 × B2`. -/
lemma box_1_1_1 (x y z : ℝ) (hx1 : (121/64:ℝ) ≤ x) (hx2 : x ≤ (141/64:ℝ))
    (hy1 : (121/64:ℝ) ≤ y) (hy2 : y ≤ (141/64:ℝ))
    (hz1 : (121/64:ℝ) ≤ z) (hz2 : z ≤ (141/64:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  exact ch_219 x y z (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith)

end Zeta23Ext.Bridge.FourPoint
