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
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  exact ch_0 x y z (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith)

set_option maxHeartbeats 20000000 in
/-- The box `B1 × B1 × B2`. -/
lemma box_0_0_1 (x y z : ℝ) (hx1 : (63/64:ℝ) ≤ x) (hx2 : x ≤ (73/64:ℝ))
    (hy1 : (63/64:ℝ) ≤ y) (hy2 : y ≤ (73/64:ℝ))
    (hz1 : (121/64:ℝ) ≤ z) (hz2 : z ≤ (141/64:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  exact ch_1 x y z (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith)

set_option maxHeartbeats 20000000 in
/-- The box `B1 × B1 × B3`. -/
lemma box_0_0_2 (x y z : ℝ) (hx1 : (63/64:ℝ) ≤ x) (hx2 : x ≤ (73/64:ℝ))
    (hy1 : (63/64:ℝ) ≤ y) (hy2 : y ≤ (73/64:ℝ))
    (hz1 : (179/64:ℝ) ≤ z) (hz2 : z ≤ (105/32:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  exact ch_2 x y z (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith)

set_option maxHeartbeats 20000000 in
/-- The box `B1 × B1 × B4`. -/
lemma box_0_0_3 (x y z : ℝ) (hx1 : (63/64:ℝ) ≤ x) (hx2 : x ≤ (73/64:ℝ))
    (hy1 : (63/64:ℝ) ≤ y) (hy2 : y ≤ (73/64:ℝ))
    (hz1 : (237/64:ℝ) ≤ z) (hz2 : z ≤ (231/40:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  exact ch_3 x y z (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith)

set_option maxHeartbeats 20000000 in
/-- The box `B1 × B2 × B1`. -/
lemma box_0_1_0 (x y z : ℝ) (hx1 : (63/64:ℝ) ≤ x) (hx2 : x ≤ (73/64:ℝ))
    (hy1 : (121/64:ℝ) ≤ y) (hy2 : y ≤ (141/64:ℝ))
    (hz1 : (63/64:ℝ) ≤ z) (hz2 : z ≤ (73/64:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  rcases le_total y (131/64:ℝ) with hc | hc
  · rcases le_total x (17/16:ℝ) with hc | hc
    · rcases le_total y (63/32:ℝ) with hc | hc
      · exact ch_4 x y z (by linarith) (by linarith) (by linarith)
          (by linarith) (by linarith) (by linarith)
      · rcases le_total z (17/16:ℝ) with hc | hc
        · rcases le_total x (131/128:ℝ) with hc | hc
          · exact ch_5 x y z (by linarith) (by linarith) (by linarith)
              (by linarith) (by linarith) (by linarith)
          · rcases le_total y (257/128:ℝ) with hc | hc
            · rcases le_total z (131/128:ℝ) with hc | hc
              · exact ch_6 x y z (by linarith) (by linarith) (by linarith)
                  (by linarith) (by linarith) (by linarith)
              · rcases le_total x (267/256:ℝ) with hc | hc
                · rcases le_total y (509/256:ℝ) with hc | hc
                  · rcases le_total z (267/256:ℝ) with hc | hc
                    · exact ch_7 x y z (by linarith) (by linarith) (by linarith)
                        (by linarith) (by linarith) (by linarith)
                    · rcases le_total x (529/512:ℝ) with hc | hc
                      · exact ch_8 x y z (by linarith) (by linarith) (by linarith)
                          (by linarith) (by linarith) (by linarith)
                      · rcases le_total y (1013/512:ℝ) with hc | hc
                        · exact ch_9 x y z (by linarith) (by linarith) (by linarith)
                            (by linarith) (by linarith) (by linarith)
                        · rcases le_total z (539/512:ℝ) with hc | hc
                          · rcases le_total x (1063/1024:ℝ) with hc | hc
                            · exact ch_10 x y z (by linarith) (by linarith) (by linarith)
                                (by linarith) (by linarith) (by linarith)
                            · rcases le_total y (2031/1024:ℝ) with hc | hc
                              · exact ch_11 x y z (by linarith) (by linarith) (by linarith)
                                  (by linarith) (by linarith) (by linarith)
                              · exact ch_12 x y z (by linarith) (by linarith) (by linarith)
                                  (by linarith) (by linarith) (by linarith)
                          · exact ch_13 x y z (by linarith) (by linarith) (by linarith)
                              (by linarith) (by linarith) (by linarith)
                  · rcases le_total z (267/256:ℝ) with hc | hc
                    · exact ch_14 x y z (by linarith) (by linarith) (by linarith)
                        (by linarith) (by linarith) (by linarith)
                    · rcases le_total x (529/512:ℝ) with hc | hc
                      · exact ch_15 x y z (by linarith) (by linarith) (by linarith)
                          (by linarith) (by linarith) (by linarith)
                      · exact ch_16 x y z (by linarith) (by linarith) (by linarith)
                          (by linarith) (by linarith) (by linarith)
                · rcases le_total y (509/256:ℝ) with hc | hc
                  · rcases le_total z (267/256:ℝ) with hc | hc
                    · rcases le_total x (539/512:ℝ) with hc | hc
                      · rcases le_total y (1013/512:ℝ) with hc | hc
                        · exact ch_17 x y z (by linarith) (by linarith) (by linarith)
                            (by linarith) (by linarith) (by linarith)
                        · rcases le_total z (529/512:ℝ) with hc | hc
                          · exact ch_18 x y z (by linarith) (by linarith) (by linarith)
                              (by linarith) (by linarith) (by linarith)
                          · rcases le_total x (1073/1024:ℝ) with hc | hc
                            · exact ch_19 x y z (by linarith) (by linarith) (by linarith)
                                (by linarith) (by linarith) (by linarith)
                            · exact ch_20 x y z (by linarith) (by linarith) (by linarith)
                                (by linarith) (by linarith) (by linarith)
                      · exact ch_21 x y z (by linarith) (by linarith) (by linarith)
                          (by linarith) (by linarith) (by linarith)
                    · rcases le_total x (539/512:ℝ) with hc | hc
                      · rcases le_total y (1013/512:ℝ) with hc | hc
                        · rcases le_total z (539/512:ℝ) with hc | hc
                          · rcases le_total x (1073/1024:ℝ) with hc | hc
                            · rcases le_total y (2021/1024:ℝ) with hc | hc
                              · exact ch_22 x y z (by linarith) (by linarith) (by linarith)
                                  (by linarith) (by linarith) (by linarith)
                              · rcases le_total z (1073/1024:ℝ) with hc | hc
                                · exact ch_23 x y z (by linarith) (by linarith) (by linarith)
                                    (by linarith) (by linarith) (by linarith)
                                · exact ch_24 x y z (by linarith) (by linarith) (by linarith)
                                    (by linarith) (by linarith) (by linarith)
                            · rcases le_total y (2021/1024:ℝ) with hc | hc
                              · exact ch_25 x y z (by linarith) (by linarith) (by linarith)
                                  (by linarith) (by linarith) (by linarith)
                              · exact ch_26 x y z (by linarith) (by linarith) (by linarith)
                                  (by linarith) (by linarith) (by linarith)
                          · exact ch_27 x y z (by linarith) (by linarith) (by linarith)
                              (by linarith) (by linarith) (by linarith)
                        · rcases le_total z (539/512:ℝ) with hc | hc
                          · rcases le_total x (1073/1024:ℝ) with hc | hc
                            · rcases le_total y (2031/1024:ℝ) with hc | hc
                              · rcases le_total z (1073/1024:ℝ) with hc | hc
                                · rcases le_total x (2141/2048:ℝ) with hc | hc
                                  · exact ch_28 x y z (by linarith) (by linarith) (by linarith)
                                      (by linarith) (by linarith) (by linarith)
                                  · exact ch_29 x y z (by linarith) (by linarith) (by linarith)
                                      (by linarith) (by linarith) (by linarith)
                                · exact ch_30 x y z (by linarith) (by linarith) (by linarith)
                                    (by linarith) (by linarith) (by linarith)
                              · rcases le_total z (1073/1024:ℝ) with hc | hc
                                · rcases le_total x (2141/2048:ℝ) with hc | hc
                                  · exact ch_31 x y z (by linarith) (by linarith) (by linarith)
                                      (by linarith) (by linarith) (by linarith)
                                  · exact ch_32 x y z (by linarith) (by linarith) (by linarith)
                                      (by linarith) (by linarith) (by linarith)
                                · exact ch_33 x y z (by linarith) (by linarith) (by linarith)
                                    (by linarith) (by linarith) (by linarith)
                            · rcases le_total y (2031/1024:ℝ) with hc | hc
                              · rcases le_total z (1073/1024:ℝ) with hc | hc
                                · exact ch_34 x y z (by linarith) (by linarith) (by linarith)
                                    (by linarith) (by linarith) (by linarith)
                                · exact ch_35 x y z (by linarith) (by linarith) (by linarith)
                                    (by linarith) (by linarith) (by linarith)
                              · exact ch_36 x y z (by linarith) (by linarith) (by linarith)
                                  (by linarith) (by linarith) (by linarith)
                          · exact ch_37 x y z (by linarith) (by linarith) (by linarith)
                              (by linarith) (by linarith) (by linarith)
                      · exact ch_38 x y z (by linarith) (by linarith) (by linarith)
                          (by linarith) (by linarith) (by linarith)
                  · rcases le_total z (267/256:ℝ) with hc | hc
                    · rcases le_total x (539/512:ℝ) with hc | hc
                      · rcases le_total y (1023/512:ℝ) with hc | hc
                        · exact ch_39 x y z (by linarith) (by linarith) (by linarith)
                            (by linarith) (by linarith) (by linarith)
                        · exact ch_40 x y z (by linarith) (by linarith) (by linarith)
                            (by linarith) (by linarith) (by linarith)
                      · exact ch_41 x y z (by linarith) (by linarith) (by linarith)
                          (by linarith) (by linarith) (by linarith)
                    · rcases le_total x (539/512:ℝ) with hc | hc
                      · rcases le_total y (1023/512:ℝ) with hc | hc
                        · rcases le_total z (539/512:ℝ) with hc | hc
                          · rcases le_total x (1073/1024:ℝ) with hc | hc
                            · exact ch_42 x y z (by linarith) (by linarith) (by linarith)
                                (by linarith) (by linarith) (by linarith)
                            · exact ch_43 x y z (by linarith) (by linarith) (by linarith)
                                (by linarith) (by linarith) (by linarith)
                          · exact ch_44 x y z (by linarith) (by linarith) (by linarith)
                              (by linarith) (by linarith) (by linarith)
                        · exact ch_45 x y z (by linarith) (by linarith) (by linarith)
                            (by linarith) (by linarith) (by linarith)
                      · exact ch_46 x y z (by linarith) (by linarith) (by linarith)
                          (by linarith) (by linarith) (by linarith)
            · exact ch_47 x y z (by linarith) (by linarith) (by linarith)
                (by linarith) (by linarith) (by linarith)
        · exact ch_48 x y z (by linarith) (by linarith) (by linarith)
            (by linarith) (by linarith) (by linarith)
    · exact ch_49 x y z (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith)
  · exact ch_50 x y z (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith) (by linarith)

set_option maxHeartbeats 20000000 in
/-- The box `B1 × B2 × B2`. -/
lemma box_0_1_1 (x y z : ℝ) (hx1 : (63/64:ℝ) ≤ x) (hx2 : x ≤ (73/64:ℝ))
    (hy1 : (121/64:ℝ) ≤ y) (hy2 : y ≤ (141/64:ℝ))
    (hz1 : (121/64:ℝ) ≤ z) (hz2 : z ≤ (141/64:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  rcases le_total y (131/64:ℝ) with hc | hc
  · rcases le_total z (131/64:ℝ) with hc | hc
    · rcases le_total x (17/16:ℝ) with hc | hc
      · rcases le_total y (63/32:ℝ) with hc | hc
        · exact ch_51 x y z (by linarith) (by linarith) (by linarith)
            (by linarith) (by linarith) (by linarith)
        · rcases le_total z (63/32:ℝ) with hc | hc
          · exact ch_52 x y z (by linarith) (by linarith) (by linarith)
              (by linarith) (by linarith) (by linarith)
          · rcases le_total x (131/128:ℝ) with hc | hc
            · exact ch_53 x y z (by linarith) (by linarith) (by linarith)
                (by linarith) (by linarith) (by linarith)
            · rcases le_total y (257/128:ℝ) with hc | hc
              · rcases le_total z (257/128:ℝ) with hc | hc
                · exact ch_54 x y z (by linarith) (by linarith) (by linarith)
                    (by linarith) (by linarith) (by linarith)
                · exact ch_55 x y z (by linarith) (by linarith) (by linarith)
                    (by linarith) (by linarith) (by linarith)
              · exact ch_56 x y z (by linarith) (by linarith) (by linarith)
                  (by linarith) (by linarith) (by linarith)
      · exact ch_57 x y z (by linarith) (by linarith) (by linarith)
          (by linarith) (by linarith) (by linarith)
    · exact ch_58 x y z (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith)
  · exact ch_59 x y z (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith) (by linarith)

set_option maxHeartbeats 20000000 in
/-- The box `B1 × B2 × B3`. -/
lemma box_0_1_2 (x y z : ℝ) (hx1 : (63/64:ℝ) ≤ x) (hx2 : x ≤ (73/64:ℝ))
    (hy1 : (121/64:ℝ) ≤ y) (hy2 : y ≤ (141/64:ℝ))
    (hz1 : (179/64:ℝ) ≤ z) (hz2 : z ≤ (105/32:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  exact ch_60 x y z (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith)

set_option maxHeartbeats 20000000 in
/-- The box `B1 × B3 × B1`. -/
lemma box_0_2_0 (x y z : ℝ) (hx1 : (63/64:ℝ) ≤ x) (hx2 : x ≤ (73/64:ℝ))
    (hy1 : (179/64:ℝ) ≤ y) (hy2 : y ≤ (105/32:ℝ))
    (hz1 : (63/64:ℝ) ≤ z) (hz2 : z ≤ (73/64:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  rcases le_total y (389/128:ℝ) with hc | hc
  · rcases le_total y (747/256:ℝ) with hc | hc
    · exact ch_61 x y z (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith)
    · rcases le_total x (17/16:ℝ) with hc | hc
      · rcases le_total z (17/16:ℝ) with hc | hc
        · rcases le_total y (1525/512:ℝ) with hc | hc
          · exact ch_62 x y z (by linarith) (by linarith) (by linarith)
              (by linarith) (by linarith) (by linarith)
          · exact ch_63 x y z (by linarith) (by linarith) (by linarith)
              (by linarith) (by linarith) (by linarith)
        · exact ch_64 x y z (by linarith) (by linarith) (by linarith)
            (by linarith) (by linarith) (by linarith)
      · exact ch_65 x y z (by linarith) (by linarith) (by linarith)
          (by linarith) (by linarith) (by linarith)
  · exact ch_66 x y z (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith) (by linarith)

set_option maxHeartbeats 20000000 in
/-- The box `B1 × B3 × B2`. -/
lemma box_0_2_1 (x y z : ℝ) (hx1 : (63/64:ℝ) ≤ x) (hx2 : x ≤ (73/64:ℝ))
    (hy1 : (179/64:ℝ) ≤ y) (hy2 : y ≤ (105/32:ℝ))
    (hz1 : (121/64:ℝ) ≤ z) (hz2 : z ≤ (141/64:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  exact ch_67 x y z (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith)

set_option maxHeartbeats 20000000 in
/-- The box `B1 × B4 × B1`. -/
lemma box_0_3_0 (x y z : ℝ) (hx1 : (63/64:ℝ) ≤ x) (hx2 : x ≤ (73/64:ℝ))
    (hy1 : (237/64:ℝ) ≤ y) (hy2 : y ≤ (231/40:ℝ))
    (hz1 : (63/64:ℝ) ≤ z) (hz2 : z ≤ (73/64:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  exact ch_68 x y z (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith)

set_option maxHeartbeats 20000000 in
/-- The box `B2 × B1 × B2`. -/
lemma box_1_0_1 (x y z : ℝ) (hx1 : (121/64:ℝ) ≤ x) (hx2 : x ≤ (141/64:ℝ))
    (hy1 : (63/64:ℝ) ≤ y) (hy2 : y ≤ (73/64:ℝ))
    (hz1 : (121/64:ℝ) ≤ z) (hz2 : z ≤ (141/64:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  rcases le_total x (131/64:ℝ) with hc | hc
  · rcases le_total z (131/64:ℝ) with hc | hc
    · rcases le_total x (63/32:ℝ) with hc | hc
      · exact ch_69 x y z (by linarith) (by linarith) (by linarith)
          (by linarith) (by linarith) (by linarith)
      · rcases le_total y (17/16:ℝ) with hc | hc
        · exact ch_70 x y z (by linarith) (by linarith) (by linarith)
            (by linarith) (by linarith) (by linarith)
        · exact ch_71 x y z (by linarith) (by linarith) (by linarith)
            (by linarith) (by linarith) (by linarith)
    · exact ch_72 x y z (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith)
  · exact ch_73 x y z (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith) (by linarith)

set_option maxHeartbeats 20000000 in
/-- The box `B2 × B1 × B3`. -/
lemma box_1_0_2 (x y z : ℝ) (hx1 : (121/64:ℝ) ≤ x) (hx2 : x ≤ (141/64:ℝ))
    (hy1 : (63/64:ℝ) ≤ y) (hy2 : y ≤ (73/64:ℝ))
    (hz1 : (179/64:ℝ) ≤ z) (hz2 : z ≤ (105/32:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  exact ch_74 x y z (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith)

set_option maxHeartbeats 20000000 in
/-- The box `B2 × B2 × B2`. -/
lemma box_1_1_1 (x y z : ℝ) (hx1 : (121/64:ℝ) ≤ x) (hx2 : x ≤ (141/64:ℝ))
    (hy1 : (121/64:ℝ) ≤ y) (hy2 : y ≤ (141/64:ℝ))
    (hz1 : (121/64:ℝ) ≤ z) (hz2 : z ≤ (141/64:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  exact ch_75 x y z (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith)

end Zeta23Ext.Bridge.FourPoint
