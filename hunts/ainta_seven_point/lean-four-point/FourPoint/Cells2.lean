import FourPoint.Base

noncomputable section
open Real
namespace Zeta23Ext.Bridge.FourPoint


theorem wc_120 (x : ℝ) (h₁ : (499/256:ℝ) ≤ x) (h₂ : x ≤ (2001/1024:ℝ)) : (10794742611/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (72097097/500000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (79767001/500000000:ℝ) := by nlinarith
  have hc1 : (493650707943/500000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (493650707943/500000000000:ℝ) ≤ taylorCos (79767001/500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (494811009867/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (72097097/500000000:ℝ) + taylorErr ≤ (494811009867/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (35923757707/250000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (35923757707/250000000000:ℝ) ≤ taylorSin (72097097/500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (31771629131/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (79767001/500000000:ℝ) + taylorErr ≤ (31771629131/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (493650707943/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (494811009867/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-31771629131/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-35923757707/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6123651305239/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6138991113119/1000000000000:ℝ) := by nlinarith
  have hp1 : (5067317111579/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (406400868789/40000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1614002210211/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1456296577127/1000000000000:ℝ) := by nlinarith
  have hN : (2443597993013/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (74374423773909/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2443597993013/1000000000000:ℝ) (74374423773909/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (10794742611/10000000000000:ℝ) ≤ ((2443597993013/1000000000000:ℝ)/(74374423773909/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_121 (x : ℝ) (h₁ : (499/256:ℝ) ≤ x) (h₂ : x ≤ (1003/512:ℝ)) : (9381492901/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1288543861/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (79767001/500000000:ℝ) := by nlinarith
  have hc1 : (493650707943/500000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (493650707943/500000000000:ℝ) ≤ taylorCos (79767001/500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (495854877971/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1288543861/10000000000:ℝ) + taylorErr ≤ (495854877971/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (2569962169/20000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (2569962169/20000000000:ℝ) ≤ taylorSin (1288543861/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (31771629131/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (79767001/500000000:ℝ) + taylorErr ≤ (31771629131/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (493650707943/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (495854877971/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-31771629131/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-2569962169/20000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6123651305239/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3077165460499/500000000000:ℝ) := by nlinarith
  have hp1 : (5067317111579/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1273176135043/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-809017599621/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-325570331877/250000000000:ℝ) := by nlinarith
  have hN : (1144791371697/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (14950315634061/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1144791371697/500000000000:ℝ) (14950315634061/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (9381492901/10000000000000:ℝ) ≤ ((1144791371697/500000000000:ℝ)/(14950315634061/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_122 (x : ℝ) (h₁ : (499/256:ℝ) ≤ x) (h₂ : x ≤ (63/32:ℝ)) : (688065547/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/1250000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (79767001/500000000:ℝ) := by nlinarith
  have hc1 : (493650707943/500000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (493650707943/500000000000:ℝ) ≤ taylorCos (79767001/500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (995184728937/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/1250000000:ℝ) + taylorErr ≤ (995184728937/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (98017138043/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (98017138043/1000000000000:ℝ) ≤ taylorSin (122718463/1250000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (31771629131/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (79767001/500000000:ℝ) + taylorErr ≤ (31771629131/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (493650707943/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (995184728937/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-31771629131/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-98017138043/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6123651305239/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1237002107351/200000000000:ℝ) := by nlinarith
  have hp1 : (5067317111579/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10236183801581/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1626101177303/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-496683920833/500000000000:ℝ) := by nlinarith
  have hN : (123791828597/62500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (75508710679541/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (123791828597/62500000000:ℝ) (75508710679541/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (688065547/1000000000000:ℝ) ≤ ((123791828597/62500000000:ℝ)/(75508710679541/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_123 (x : ℝ) (h₁ : (2001/1024:ℝ) ≤ x) (h₂ : x ≤ (1003/512:ℝ)) : (4713649797/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1288543861/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (1441941941/10000000000:ℝ) := by nlinarith
  have hc1 : (197924403039/200000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (197924403039/200000000000:ℝ) ≤ taylorCos (1441941941/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (495854877971/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1288543861/10000000000:ℝ) + taylorErr ≤ (495854877971/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (2569962169/20000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (2569962169/20000000000:ℝ) ≤ taylorSin (1288543861/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (143695035451/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1441941941/10000000000:ℝ) + taylorErr ≤ (143695035451/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (197924403039/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (495854877971/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-143695035451/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-2569962169/20000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3069495556559/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3077165460499/500000000000:ℝ) := by nlinarith
  have hp1 : (10160021583437/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1273176135043/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1463592718883/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-652771777641/500000000000:ℝ) := by nlinarith
  have hN : (2295165570477/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (14950315634061/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2295165570477/1000000000000:ℝ) (14950315634061/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (4713649797/5000000000000:ℝ) ≤ ((2295165570477/1000000000000:ℝ)/(14950315634061/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_124 (x : ℝ) (h₁ : (1003/512:ℝ) ≤ x) (h₂ : x ≤ (2011/1024:ℝ)) : (8154586159/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1135145783/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (644271931/5000000000:ℝ) := by nlinarith
  have hc1 : (198341950281/200000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (198341950281/200000000000:ℝ) ≤ taylorCos (644271931/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (993564137783/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1135145783/10000000000:ℝ) + taylorErr ≤ (993564137783/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (14158868739/125000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (14158868739/125000000000:ℝ) ≤ taylorSin (1135145783/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (128498113073/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (644271931/5000000000:ℝ) + taylorErr ≤ (128498113073/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (198341950281/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (993564137783/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-128498113073/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-14158868739/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6154330920997/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6169670728877/1000000000000:ℝ) := by nlinarith
  have hp1 : (2546352235929/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2552699110241/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1312068075637/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-144213868287/125000000000:ℝ) := by nlinarith
  have hN : (2145420697701/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (18782418451381/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2145420697701/1000000000000:ℝ) (18782418451381/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (8154586159/10000000000000:ℝ) ≤ ((2145420697701/1000000000000:ℝ)/(18782418451381/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_125 (x : ℝ) (h₁ : (1003/512:ℝ) ≤ x) (h₂ : x ≤ (63/32:ℝ)) : (694601603/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/1250000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (644271931/5000000000:ℝ) := by nlinarith
  have hc1 : (198341950281/200000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (198341950281/200000000000:ℝ) ≤ taylorCos (644271931/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (995184728937/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/1250000000:ℝ) + taylorErr ≤ (995184728937/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (98017138043/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (98017138043/1000000000000:ℝ) ≤ taylorSin (122718463/1250000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (128498113073/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (644271931/5000000000:ℝ) + taylorErr ≤ (128498113073/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (198341950281/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (995184728937/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-128498113073/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-98017138043/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6154330920997/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1237002107351/200000000000:ℝ) := by nlinarith
  have hp1 : (2546352235929/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10236183801581/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-328832575893/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-49917231723/50000000000:ℝ) := by nlinarith
  have hN : (398010877173/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (75508710679541/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (398010877173/200000000000:ℝ) (75508710679541/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (694601603/1000000000000:ℝ) ≤ ((398010877173/200000000000:ℝ)/(75508710679541/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_126 (x : ℝ) (h₁ : (2011/1024:ℝ) ≤ x) (h₂ : x ≤ (4027/2048:ℝ)) : (118281741/156250000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1058446743/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (141893223/1250000000:ℝ) := by nlinarith
  have hc1 : (7762219791/7812500000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (7762219791/7812500000:ℝ) ≤ taylorCos (141893223/1250000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (994403682327/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1058446743/10000000000:ℝ) + taylorErr ≤ (994403682327/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (26411787847/250000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (26411787847/250000000000:ℝ) ≤ taylorSin (1058446743/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (14158869317/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (141893223/1250000000:ℝ) + taylorErr ≤ (14158869317/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (7762219791/7812500000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (994403682327/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-14158869317/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-26411787847/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1542417682219/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (386083789551/62500000000:ℝ) := by nlinarith
  have hp1 : (5105398151997/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10223490121273/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-579012242363/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-26968538573/25000000000:ℝ) := by nlinarith
  have hN : (259038209521/125000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (470744216173/6250000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (259038209521/125000000000:ℝ) (470744216173/6250000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (118281741/156250000000:ℝ) ≤ ((259038209521/125000000000:ℝ)/(470744216173/6250000000:ℝ))^2 := by norm_num
  linarith

theorem wc_127 (x : ℝ) (h₁ : (2011/1024:ℝ) ≤ x) (h₂ : x ≤ (63/32:ℝ)) : (697636487/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/1250000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (141893223/1250000000:ℝ) := by nlinarith
  have hc1 : (7762219791/7812500000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (7762219791/7812500000:ℝ) ≤ taylorCos (141893223/1250000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (995184728937/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/1250000000:ℝ) + taylorErr ≤ (995184728937/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (98017138043/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (98017138043/1000000000000:ℝ) ≤ taylorSin (122718463/1250000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (14158869317/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (141893223/1250000000:ℝ) + taylorErr ≤ (14158869317/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (7762219791/7812500000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (995184728937/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-14158869317/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-98017138043/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1542417682219/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1237002107351/200000000000:ℝ) := by nlinarith
  have hp1 : (5105398151997/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10236183801581/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-289865577503/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1000833030857/1000000000000:ℝ) := by nlinarith
  have hN : (398879432821/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (75508710679541/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (398879432821/200000000000:ℝ) (75508710679541/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (697636487/1000000000000:ℝ) ≤ ((398879432821/200000000000:ℝ)/(75508710679541/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_128 (x : ℝ) (h₁ : (4027/2048:ℝ) ≤ x) (h₂ : x ≤ (63/32:ℝ)) : (6990950273/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/1250000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (132305843/1250000000:ℝ) := by nlinarith
  have hc1 : (31075114931/31250000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (31075114931/31250000000:ℝ) ≤ taylorCos (132305843/1250000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (995184728937/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/1250000000:ℝ) + taylorErr ≤ (995184728937/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (98017138043/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (98017138043/1000000000000:ℝ) ≤ taylorSin (122718463/1250000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (105647156011/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (132305843/1250000000:ℝ) + taylorErr ≤ (105647156011/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (31075114931/31250000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (995184728937/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-105647156011/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-98017138043/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1235468126563/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1237002107351/200000000000:ℝ) := by nlinarith
  have hp1 : (10223489984133/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10236183801581/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1081423707043/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-200415445811/200000000000:ℝ) := by nlinarith
  have hN : (1996480906847/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (75508710679541/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1996480906847/1000000000000:ℝ) (75508710679541/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (6990950273/10000000000000:ℝ) ≤ ((1996480906847/1000000000000:ℝ)/(75508710679541/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_129 (x : ℝ) (h₁ : (63/32:ℝ) ≤ x) (h₂ : x ≤ (8069/4096:ℝ)) : (1679250671/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (117924773/1250000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (196349541/2000000000:ℝ) := by nlinarith
  have hc1 : (995184724403/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (995184724403/1000000000000:ℝ) ≤ taylorCos (196349541/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (995553301033/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (117924773/1250000000:ℝ) + taylorErr ≤ (995553301033/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (94199940979/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (94199940979/1000000000000:ℝ) ≤ taylorSin (117924773/1250000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (98017142667/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (196349541/2000000000:ℝ) + taylorErr ≤ (98017142667/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (995184724403/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (995553301033/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-98017142667/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-94199940979/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3092505268377/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (247553819549/40000000000:ℝ) := by nlinarith
  have hp1 : (10236183664271/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10242530641737/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1003943587183/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-15066373391/15625000000:ℝ) := by nlinarith
  have hN : (1959432621427/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (2362613030207/31250000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1959432621427/1000000000000:ℝ) (2362613030207/31250000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1679250671/2500000000000:ℝ) ≤ ((1959432621427/1000000000000:ℝ)/(2362613030207/31250000000:ℝ))^2 := by norm_num
  linarith

theorem wc_130 (x : ℝ) (h₁ : (63/32:ℝ) ≤ x) (h₂ : x ≤ (4037/2048:ℝ)) : (6435510271/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (113131083/1250000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (196349541/2000000000:ℝ) := by nlinarith
  have hc1 : (995184724403/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (995184724403/1000000000000:ℝ) ≤ taylorCos (196349541/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (995907231687/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (113131083/1250000000:ℝ) + taylorErr ≤ (995907231687/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (90381358531/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (90381358531/1000000000000:ℝ) ≤ taylorSin (113131083/1250000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (98017142667/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (196349541/2000000000:ℝ) + taylorErr ≤ (98017142667/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (995184724403/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (995907231687/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-98017142667/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-90381358531/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3092505268377/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1238536088139/200000000000:ℝ) := by nlinarith
  have hp1 : (10236183664271/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2562219370473/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-12557071079/12500000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-925160185749/1000000000000:ℝ) := by nlinarith
  have hN : (240043113769/125000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (75698582081133/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (240043113769/125000000000:ℝ) (75698582081133/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (6435510271/10000000000000:ℝ) ≤ ((240043113769/125000000000:ℝ)/(75698582081133/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_131 (x : ℝ) (h₁ : (63/32:ℝ) ≤ x) (h₂ : x ≤ (2021/1024:ℝ)) : (2946158453/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (6626797/80000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (196349541/2000000000:ℝ) := by nlinarith
  have hc1 : (995184724403/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (995184724403/1000000000000:ℝ) ≤ taylorCos (196349541/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (124571393507/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (6626797/80000000:ℝ) + taylorErr ≤ (124571393507/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (41370131121/500000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (41370131121/500000000000:ℝ) ≤ taylorSin (6626797/80000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (98017142667/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (196349541/2000000000:ℝ) + taylorErr ≤ (98017142667/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (995184724403/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (124571393507/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-98017142667/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-41370131121/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3092505268377/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3100175172317/500000000000:ℝ) := by nlinarith
  have hp1 : (10236183664271/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10261571162201/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-502904942297/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-846944520739/1000000000000:ℝ) := by nlinarith
  have hN : (921064622571/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (37944344396203/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (921064622571/500000000000:ℝ) (37944344396203/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2946158453/5000000000000:ℝ) ≤ ((921064622571/500000000000:ℝ)/(37944344396203/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_132 (x : ℝ) (h₁ : (63/32:ℝ) ≤ x) (h₂ : x ≤ (1013/512:ℝ)) : (4884069333/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (337475773/5000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (196349541/2000000000:ℝ) := by nlinarith
  have hc1 : (995184724403/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (995184724403/1000000000000:ℝ) ≤ taylorCos (196349541/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (997723068911/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (337475773/5000000000:ℝ) + taylorErr ≤ (997723068911/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (13488783447/200000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (13488783447/200000000000:ℝ) ≤ taylorSin (337475773/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (98017142667/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (196349541/2000000000:ℝ) + taylorErr ≤ (98017142667/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (995184724403/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (997723068911/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-98017142667/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-13488783447/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3092505268377/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6215690152513/1000000000000:ℝ) := by nlinarith
  have hp1 : (10236183664271/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (514347926141/50000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1008298281141/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-138073664771/200000000000:ℝ) := by nlinarith
  have hN : (842776524129/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (15253921628819/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (842776524129/500000000000:ℝ) (15253921628819/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (4884069333/10000000000000:ℝ) ≤ ((842776524129/500000000000:ℝ)/(15253921628819/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_133 (x : ℝ) (h₁ : (63/32:ℝ) ≤ x) (h₂ : x ≤ (509/256:ℝ)) : (396477691/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (368155389/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (196349541/2000000000:ℝ) := by nlinarith
  have hc1 : (995184724403/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (995184724403/1000000000000:ℝ) ≤ taylorCos (196349541/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (999322386851/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (368155389/10000000000:ℝ) + taylorErr ≤ (999322386851/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (3680722067/100000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (3680722067/100000000000:ℝ) ≤ taylorSin (368155389/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (98017142667/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (196349541/2000000000:ℝ) + taylorErr ≤ (98017142667/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (995184724403/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999322386851/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-98017142667/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-3680722067/100000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3092505268377/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6246369768271/1000000000000:ℝ) := by nlinarith
  have hp1 : (10236183664271/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5168866622029/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1013275074237/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-376765470949/1000000000000:ℝ) := by nlinarith
  have hN : (171493774419/125000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (3851713528197/50000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (171493774419/125000000000:ℝ) (3851713528197/50000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (396477691/1250000000000:ℝ) ≤ ((171493774419/125000000000:ℝ)/(3851713528197/50000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_134 (x : ℝ) (h₁ : (63/32:ℝ) ≤ x) (h₂ : x ≤ (2:ℝ)) : (325933483/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (196349541/2000000000:ℝ) := by nlinarith
  have hc1 : (995184724403/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (995184724403/1000000000000:ℝ) ≤ taylorCos (196349541/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (98017142667/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (196349541/2000000000:ℝ) + taylorErr ≤ (98017142667/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (995184724403/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (500000001131/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-98017142667/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1131/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3092505268377/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (314159265359/50000000000:ℝ) := by nlinarith
  have hp1 : (10236183664271/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10398662909543/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1019247225951/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (11761/500000000000:ℝ) := by nlinarith
  have hN : (995184700881/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (38978417604363/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (995184700881/1000000000000:ℝ) (38978417604363/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (325933483/2000000000000:ℝ) ≤ ((995184700881/1000000000000:ℝ)/(38978417604363/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_135 (x : ℝ) (h₁ : (8069/4096:ℝ) ≤ x) (h₂ : x ≤ (4037/2048:ℝ)) : (3220913463/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (113131083/1250000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (188679637/2000000000:ℝ) := by nlinarith
  have hc1 : (995553296499/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (995553296499/1000000000000:ℝ) ≤ taylorCos (188679637/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (995907231687/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (113131083/1250000000:ℝ) + taylorErr ≤ (995907231687/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (90381358531/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (90381358531/1000000000000:ℝ) ≤ taylorSin (113131083/1250000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (47099972801/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (188679637/2000000000:ℝ) + taylorErr ≤ (47099972801/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (995553296499/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (995907231687/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-47099972801/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-90381358531/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1547211372181/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1238536088139/200000000000:ℝ) := by nlinarith
  have hp1 : (5121265252171/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2562219370473/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-241360925319/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-925733821777/1000000000000:ℝ) := by nlinarith
  have hN : (480321779569/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (75698582081133/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (480321779569/250000000000:ℝ) (75698582081133/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (3220913463/5000000000000:ℝ) ≤ ((480321779569/250000000000:ℝ)/(75698582081133/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_136 (x : ℝ) (h₁ : (4037/2048:ℝ) ≤ x) (h₂ : x ≤ (8079/4096:ℝ)) : (6172561523/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (173339829/2000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (181009733/2000000000:ℝ) := by nlinarith
  have hc1 : (497953613577/500000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (497953613577/500000000000:ℝ) ≤ taylorCos (181009733/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (498123257843/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (173339829/2000000000:ℝ) + taylorErr ≤ (498123257843/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (86561446959/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (86561446959/1000000000000:ℝ) ≤ taylorSin (173339829/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (18076272631/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (181009733/2000000000:ℝ) + taylorErr ≤ (18076272631/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (497953613577/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (498123257843/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-18076272631/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-86561446959/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3096340220347/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1239303078533/200000000000:ℝ) := by nlinarith
  have hp1 : (2562219336103/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10255224322047/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-926881153687/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-887157652637/1000000000000:ℝ) := by nlinarith
  have hN : (1883064879791/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (75793606023069/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1883064879791/1000000000000:ℝ) (75793606023069/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (6172561523/10000000000000:ℝ) ≤ ((1883064879791/1000000000000:ℝ)/(75793606023069/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_137 (x : ℝ) (h₁ : (4037/2048:ℝ) ≤ x) (h₂ : x ≤ (2021/1024:ℝ)) : (5903663357/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (6626797/80000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (181009733/2000000000:ℝ) := by nlinarith
  have hc1 : (497953613577/500000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (497953613577/500000000000:ℝ) ≤ taylorCos (181009733/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (124571393507/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (6626797/80000000:ℝ) + taylorErr ≤ (124571393507/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (41370131121/500000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (41370131121/500000000000:ℝ) ≤ taylorSin (6626797/80000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (18076272631/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (181009733/2000000000:ℝ) + taylorErr ≤ (18076272631/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (497953613577/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (124571393507/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-18076272631/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-41370131121/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3096340220347/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3100175172317/500000000000:ℝ) := by nlinarith
  have hp1 : (2562219336103/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10261571162201/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-115931848719/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-423997399581/500000000000:ℝ) := by nlinarith
  have hN : (460975506579/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (37944344396203/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (460975506579/250000000000:ℝ) (37944344396203/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (5903663357/10000000000000:ℝ) ≤ ((460975506579/250000000000:ℝ)/(37944344396203/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_138 (x : ℝ) (h₁ : (8079/4096:ℝ) ≤ x) (h₂ : x ≤ (16163/8192:ℝ)) : (6042972143/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (169504877/2000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (433349573/5000000000:ℝ) := by nlinarith
  have hc1 : (996246511153/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (996246511153/1000000000000:ℝ) ≤ taylorCos (433349573/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (996410663629/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (169504877/2000000000:ℝ) + taylorErr ≤ (996410663629/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (84651010219/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (84651010219/1000000000000:ℝ) ≤ taylorSin (169504877/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (86561451583/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (433349573/5000000000:ℝ) + taylorErr ≤ (86561451583/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (996246511153/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (996410663629/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-86561451583/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-84651010219/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (774564424083/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6198432868649/1000000000000:ℝ) := by nlinarith
  have hp1 : (5127612092241/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10258397742123/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-443990899737/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-434057543619/500000000000:ℝ) := by nlinarith
  have hN : (1864361598391/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (75841140054297/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1864361598391/1000000000000:ℝ) (75841140054297/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (6042972143/10000000000000:ℝ) ≤ ((1864361598391/1000000000000:ℝ)/(75841140054297/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_139 (x : ℝ) (h₁ : (8079/4096:ℝ) ≤ x) (h₂ : x ≤ (2021/1024:ℝ)) : (5909199941/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (6626797/80000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (433349573/5000000000:ℝ) := by nlinarith
  have hc1 : (996246511153/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (996246511153/1000000000000:ℝ) ≤ taylorCos (433349573/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (124571393507/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (6626797/80000000:ℝ) + taylorErr ≤ (124571393507/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (41370131121/500000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (41370131121/500000000000:ℝ) ≤ taylorSin (6626797/80000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (86561451583/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (433349573/5000000000:ℝ) + taylorErr ≤ (86561451583/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (996246511153/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (124571393507/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-86561451583/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-41370131121/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (774564424083/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3100175172317/500000000000:ℝ) := by nlinarith
  have hp1 : (5127612092241/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10261571162201/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-888256495323/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-424259969187/500000000000:ℝ) := by nlinarith
  have hN : (1844766449527/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (37944344396203/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1844766449527/1000000000000:ℝ) (37944344396203/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (5909199941/10000000000000:ℝ) ≤ ((1844766449527/1000000000000:ℝ)/(37944344396203/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_140 (x : ℝ) (h₁ : (16163/8192:ℝ) ≤ x) (h₂ : x ≤ (2021/1024:ℝ)) : (5911934001/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (6626797/80000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (423762193/5000000000:ℝ) := by nlinarith
  have hc1 : (124551332387/125000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (124551332387/125000000000:ℝ) ≤ taylorCos (423762193/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (124571393507/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (6626797/80000000:ℝ) + taylorErr ≤ (124571393507/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (41370131121/500000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (41370131121/500000000000:ℝ) ≤ taylorSin (6626797/80000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (84651014843/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (423762193/5000000000:ℝ) + taylorErr ≤ (84651014843/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (124551332387/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (124571393507/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-84651014843/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-41370131121/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (774804108581/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3100175172317/500000000000:ℝ) := by nlinarith
  have hp1 : (2051679520903/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10261571162201/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-217163103191/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-42439125399/50000000000:ℝ) := by nlinarith
  have hN : (461298291769/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (37944344396203/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (461298291769/250000000000:ℝ) (37944344396203/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (5911934001/10000000000000:ℝ) ≤ ((461298291769/250000000000:ℝ)/(37944344396203/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_141 (x : ℝ) (h₁ : (2021/1024:ℝ) ≤ x) (h₂ : x ≤ (16173/8192:ℝ)) : (5782371603/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (161834973/2000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (414174813/5000000000:ℝ) := by nlinarith
  have hc1 : (249142785881/250000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (249142785881/250000000000:ℝ) ≤ taylorCos (414174813/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (498363984189/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (161834973/2000000000:ℝ) + taylorErr ≤ (498363984189/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (20207302513/250000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (20207302513/250000000000:ℝ) ≤ taylorSin (161834973/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (41370133433/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (414174813/5000000000:ℝ) + taylorErr ≤ (41370133433/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (249142785881/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (498363984189/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-41370133433/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-20207302513/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6200350344633/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6202267820619/1000000000000:ℝ) := by nlinarith
  have hp1 : (205231420491/20000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5132372291139/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-16986154121/20000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-414717339903/500000000000:ℝ) := by nlinarith
  have hN : (182600582333/100000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (18984063059343/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (182600582333/100000000000:ℝ) (18984063059343/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (5782371603/10000000000000:ℝ) ≤ ((182600582333/100000000000:ℝ)/(18984063059343/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_142 (x : ℝ) (h₁ : (2021/1024:ℝ) ≤ x) (h₂ : x ≤ (8089/4096:ℝ)) : (2825867677/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (158000021/2000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (414174813/5000000000:ℝ) := by nlinarith
  have hc1 : (249142785881/250000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (249142785881/250000000000:ℝ) ≤ taylorCos (414174813/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (62305070251/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (158000021/2000000000:ℝ) + taylorErr ≤ (62305070251/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (78917860677/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (78917860677/1000000000000:ℝ) ≤ taylorSin (158000021/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (41370133433/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (414174813/5000000000:ℝ) + taylorErr ≤ (41370133433/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (249142785881/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (62305070251/62500000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-41370133433/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-78917860677/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6200350344633/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1551046324151/250000000000:ℝ) := by nlinarith
  have hp1 : (205231420491/20000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2566979500589/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-424785137837/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-404910616221/500000000000:ℝ) := by nlinarith
  have hN : (903196187983/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (15196766077839/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (903196187983/500000000000:ℝ) (15196766077839/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2825867677/5000000000000:ℝ) ≤ ((903196187983/500000000000:ℝ)/(15196766077839/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_143 (x : ℝ) (h₁ : (2021/1024:ℝ) ≤ x) (h₂ : x ≤ (4047/2048:ℝ)) : (107907129/200000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (375825293/5000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (414174813/5000000000:ℝ) := by nlinarith
  have hc1 : (249142785881/250000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (249142785881/250000000000:ℝ) ≤ taylorCos (414174813/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (498588219499/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (375825293/5000000000:ℝ) + taylorErr ≤ (498588219499/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (75094298579/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (75094298579/1000000000000:ℝ) ≤ taylorSin (375825293/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (41370133433/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (414174813/5000000000:ℝ) + taylorErr ≤ (41370133433/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (249142785881/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (498588219499/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-41370133433/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-75094298579/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6200350344633/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3104010124287/500000000000:ℝ) := by nlinarith
  have hp1 : (205231420491/20000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10274264842511/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-425047707461/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-770585478407/1000000000000:ℝ) := by nlinarith
  have hN : (1767156621931/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (7607903081341/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1767156621931/1000000000000:ℝ) (7607903081341/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (107907129/200000000000:ℝ) ≤ ((1767156621931/1000000000000:ℝ)/(7607903081341/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_144 (x : ℝ) (h₁ : (2021/1024:ℝ) ≤ x) (h₂ : x ≤ (1013/512:ℝ)) : (4902043129/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (337475773/5000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (414174813/5000000000:ℝ) := by nlinarith
  have hc1 : (249142785881/250000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (249142785881/250000000000:ℝ) ≤ taylorCos (414174813/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (997723068911/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (337475773/5000000000:ℝ) + taylorErr ≤ (997723068911/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (13488783447/200000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (13488783447/200000000000:ℝ) ≤ taylorSin (337475773/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (41370133433/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (414174813/5000000000:ℝ) + taylorErr ≤ (41370133433/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (249142785881/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (997723068911/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-41370133433/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-13488783447/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6200350344633/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6215690152513/1000000000000:ℝ) := by nlinarith
  have hp1 : (205231420491/20000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (514347926141/50000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-425572846709/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2162751709/3125000000:ℝ) := by nlinarith
  have hN : (422162922601/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (15253921628819/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (422162922601/250000000000:ℝ) (15253921628819/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (4902043129/10000000000000:ℝ) ≤ ((422162922601/250000000000:ℝ)/(15253921628819/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_145 (x : ℝ) (h₁ : (16173/8192:ℝ) ≤ x) (h₂ : x ≤ (8089/4096:ℝ)) : (5654284063/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (158000021/2000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (404587433/5000000000:ℝ) := by nlinarith
  have hc1 : (199345592769/200000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (199345592769/200000000000:ℝ) ≤ taylorCos (404587433/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (62305070251/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (158000021/2000000000:ℝ) + taylorErr ≤ (62305070251/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (78917860677/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (78917860677/1000000000000:ℝ) ≤ taylorSin (158000021/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (20207303669/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (404587433/5000000000:ℝ) + taylorErr ≤ (20207303669/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (199345592769/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (62305070251/62500000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-20207303669/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-78917860677/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3101133910309/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1551046324151/250000000000:ℝ) := by nlinarith
  have hp1 : (2052948888917/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2566979500589/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-103743468561/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-405035835981/500000000000:ℝ) := by nlinarith
  have hN : (1806799635807/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (15196766077839/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1806799635807/1000000000000:ℝ) (15196766077839/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (5654284063/10000000000000:ℝ) ≤ ((1806799635807/1000000000000:ℝ)/(15196766077839/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_146 (x : ℝ) (h₁ : (8089/4096:ℝ) ≤ x) (h₂ : x ≤ (16183/8192:ℝ)) : (221106819/400000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (154165069/2000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (395000053/5000000000:ℝ) := by nlinarith
  have hc1 : (249220279871/250000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (249220279871/250000000000:ℝ) ≤ taylorCos (395000053/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (124628826801/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (154165069/2000000000:ℝ) + taylorErr ≤ (124628826801/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (77006221143/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (77006221143/1000000000000:ℝ) ≤ taylorSin (154165069/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (78917865301/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (395000053/5000000000:ℝ) + taylorErr ≤ (78917865301/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (249220279871/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (124628826801/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-78917865301/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-77006221143/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6204185296603/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6206102772589/1000000000000:ℝ) := by nlinarith
  have hp1 : (513395893231/50000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10271091422433/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-81057260937/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-790693553761/1000000000000:ℝ) := by nlinarith
  have hN : (357514934649/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (38015711623937/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (357514934649/200000000000:ℝ) (38015711623937/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (221106819/400000000000:ℝ) ≤ ((357514934649/200000000000:ℝ)/(38015711623937/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_147 (x : ℝ) (h₁ : (8089/4096:ℝ) ≤ x) (h₂ : x ≤ (4047/2048:ℝ)) : (337510039/625000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (375825293/5000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (395000053/5000000000:ℝ) := by nlinarith
  have hc1 : (249220279871/250000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (249220279871/250000000000:ℝ) ≤ taylorCos (395000053/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (498588219499/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (375825293/5000000000:ℝ) + taylorErr ≤ (498588219499/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (75094298579/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (75094298579/1000000000000:ℝ) ≤ taylorSin (375825293/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (78917865301/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (395000053/5000000000:ℝ) + taylorErr ≤ (78917865301/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (249220279871/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (498588219499/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-78917865301/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-75094298579/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6204185296603/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3104010124287/500000000000:ℝ) := by nlinarith
  have hp1 : (513395893231/50000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10274264842511/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-810823048909/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-77106208991/100000000000:ℝ) := by nlinarith
  have hN : (883971604697/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (7607903081341/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (883971604697/500000000000:ℝ) (7607903081341/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (337510039/625000000000:ℝ) ≤ ((883971604697/500000000000:ℝ)/(7607903081341/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_148 (x : ℝ) (h₁ : (16183/8192:ℝ) ≤ x) (h₂ : x ≤ (4047/2048:ℝ)) : (5402529921/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (375825293/5000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (385412673/5000000000:ℝ) := by nlinarith
  have hc1 : (249257652469/250000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (249257652469/250000000000:ℝ) ≤ taylorCos (385412673/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (498588219499/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (375825293/5000000000:ℝ) + taylorErr ≤ (498588219499/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (75094298579/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (75094298579/1000000000000:ℝ) ≤ taylorSin (375825293/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (77006225767/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (385412673/5000000000:ℝ) + taylorErr ≤ (77006225767/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (249257652469/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (498588219499/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-77006225767/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-75094298579/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1551525693147/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3104010124287/500000000000:ℝ) := by nlinarith
  have hp1 : (2054218256931/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10274264842511/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-791182358053/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-385650197831/500000000000:ℝ) := by nlinarith
  have hN : (884165502769/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (7607903081341/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (884165502769/500000000000:ℝ) (7607903081341/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (5402529921/10000000000000:ℝ) ≤ ((884165502769/500000000000:ℝ)/(7607903081341/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_149 (x : ℝ) (h₁ : (4047/2048:ℝ) ≤ x) (h₂ : x ≤ (16193/8192:ℝ)) : (5278861443/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (366237913/5000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (751650587/10000000000:ℝ) := by nlinarith
  have hc1 : (498588217233/500000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (498588217233/500000000000:ℝ) ≤ taylorCos (751650587/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (997318597263/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (366237913/5000000000:ℝ) + taylorErr ≤ (997318597263/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (9147762477/125000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (9147762477/125000000000:ℝ) ≤ taylorSin (366237913/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (75094303203/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (751650587/10000000000:ℝ) + taylorErr ≤ (75094303203/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (498588217233/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (997318597263/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-75094303203/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-9147762477/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6208020248573/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6209937724559/1000000000000:ℝ) := by nlinarith
  have hp1 : (1027426470469/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10277438262589/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-771777065041/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-375946132577/500000000000:ℝ) := by nlinarith
  have hN : (87453434981/50000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (76126653085803/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (87453434981/50000000000:ℝ) (76126653085803/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (5278861443/10000000000000:ℝ) ≤ ((87453434981/50000000000:ℝ)/(76126653085803/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_150 (x : ℝ) (h₁ : (4047/2048:ℝ) ≤ x) (h₂ : x ≤ (8099/4096:ℝ)) : (1030893657/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (356650533/5000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (751650587/10000000000:ℝ) := by nlinarith
  have hc1 : (498588217233/500000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (498588217233/500000000000:ℝ) ≤ taylorCos (751650587/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (39898283547/40000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (356650533/5000000000:ℝ) + taylorErr ≤ (39898283547/40000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (71269631983/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (71269631983/1000000000000:ℝ) ≤ taylorSin (356650533/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (75094303203/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (751650587/10000000000:ℝ) + taylorErr ≤ (75094303203/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (498588217233/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (39898283547/40000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-75094303203/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-71269631983/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6208020248573/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6211855200543/1000000000000:ℝ) := by nlinarith
  have hp1 : (1027426470469/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2056122336533/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-772015370811/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-732243064399/1000000000000:ℝ) := by nlinarith
  have hN : (345883899773/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (76174290065027/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (345883899773/200000000000:ℝ) (76174290065027/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1030893657/2000000000000:ℝ) ≤ ((345883899773/200000000000:ℝ)/(76174290065027/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_151 (x : ℝ) (h₁ : (4047/2048:ℝ) ≤ x) (h₂ : x ≤ (1013/512:ℝ)) : (1227632877/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (337475773/5000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (751650587/10000000000:ℝ) := by nlinarith
  have hc1 : (498588217233/500000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (498588217233/500000000000:ℝ) ≤ taylorCos (751650587/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (997723068911/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (337475773/5000000000:ℝ) + taylorErr ≤ (997723068911/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (13488783447/200000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (13488783447/200000000000:ℝ) ≤ taylorSin (337475773/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (75094303203/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (751650587/10000000000:ℝ) + taylorErr ≤ (75094303203/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (498588217233/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (997723068911/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-75094303203/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-13488783447/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6208020248573/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6215690152513/1000000000000:ℝ) := by nlinarith
  have hp1 : (1027426470469/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (514347926141/50000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-15449839647/20000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-692936658393/1000000000000:ℝ) := by nlinarith
  have hN : (1690113092859/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (15253921628819/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1690113092859/1000000000000:ℝ) (15253921628819/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1227632877/2500000000000:ℝ) ≤ ((1690113092859/1000000000000:ℝ)/(15253921628819/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_152 (x : ℝ) (h₁ : (16193/8192:ℝ) ≤ x) (h₂ : x ≤ (8099/4096:ℝ)) : (2578332043/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (356650533/5000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (732475827/10000000000:ℝ) := by nlinarith
  have hc1 : (249329648183/250000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (249329648183/250000000000:ℝ) ≤ taylorCos (732475827/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (39898283547/40000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (356650533/5000000000:ℝ) + taylorErr ≤ (39898283547/40000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (71269631983/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (71269631983/1000000000000:ℝ) ≤ taylorSin (356650533/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (1829552611/25000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (732475827/10000000000:ℝ) + taylorErr ≤ (1829552611/25000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (249329648183/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (39898283547/40000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-1829552611/25000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-71269631983/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3104968862279/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6211855200543/1000000000000:ℝ) := by nlinarith
  have hp1 : (411097524989/40000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2056122336533/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-188089199467/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-732469232877/1000000000000:ℝ) := by nlinarith
  have hN : (1729787825609/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (76174290065027/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1729787825609/1000000000000:ℝ) (76174290065027/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2578332043/5000000000000:ℝ) ≤ ((1729787825609/1000000000000:ℝ)/(76174290065027/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_153 (x : ℝ) (h₁ : (8099/4096:ℝ) ≤ x) (h₂ : x ≤ (32401/16384:ℝ)) : (5097185467/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (351856843/5000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (713301067/10000000000:ℝ) := by nlinarith
  have hc1 : (997457084143/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (997457084143/1000000000000:ℝ) ≤ taylorCos (713301067/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (19950499183/20000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (351856843/5000000000:ℝ) + taylorErr ≤ (19950499183/20000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (35156649681/500000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (35156649681/500000000000:ℝ) ≤ taylorSin (351856843/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (71269636607/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (713301067/10000000000:ℝ) + taylorErr ≤ (71269636607/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (997457084143/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (19950499183/20000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-71269636607/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-35156649681/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3105927600271/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (776601742317/125000000000:ℝ) := by nlinarith
  have hp1 : (10280611544759/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (80329674943/7812500000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-73280854297/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-722863717171/1000000000000:ℝ) := by nlinarith
  have hN : (860160400657/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (15239622813947/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (860160400657/500000000000:ℝ) (15239622813947/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (5097185467/10000000000000:ℝ) ≤ ((860160400657/500000000000:ℝ)/(15239622813947/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_154 (x : ℝ) (h₁ : (8099/4096:ℝ) ≤ x) (h₂ : x ≤ (16203/8192:ℝ)) : (2517968433/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (347063153/5000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (713301067/10000000000:ℝ) := by nlinarith
  have hc1 : (997457084143/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (997457084143/1000000000000:ℝ) ≤ taylorCos (713301067/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (498795956361/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (347063153/5000000000:ℝ) + taylorErr ≤ (498795956361/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (69356902111/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (69356902111/1000000000000:ℝ) ≤ taylorSin (347063153/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (71269636607/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (713301067/10000000000:ℝ) + taylorErr ≤ (71269636607/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (997457084143/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (498795956361/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-71269636607/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-69356902111/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3105927600271/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (388360792283/62500000000:ℝ) := by nlinarith
  have hp1 : (10280611544759/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5141892551371/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-732921627217/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-713031368551/1000000000000:ℝ) := by nlinarith
  have hN : (855244226347/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (19055485437783/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (855244226347/500000000000:ℝ) (19055485437783/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2517968433/5000000000000:ℝ) ≤ ((855244226347/500000000000:ℝ)/(19055485437783/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_155 (x : ℝ) (h₁ : (8099/4096:ℝ) ≤ x) (h₂ : x ≤ (1013/512:ℝ)) : (2457325291/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (337475773/5000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (713301067/10000000000:ℝ) := by nlinarith
  have hc1 : (997457084143/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (997457084143/1000000000000:ℝ) ≤ taylorCos (713301067/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (997723068911/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (337475773/5000000000:ℝ) + taylorErr ≤ (997723068911/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (13488783447/200000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (13488783447/200000000000:ℝ) ≤ taylorSin (337475773/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (71269636607/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (713301067/10000000000:ℝ) + taylorErr ≤ (71269636607/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (997457084143/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (997723068911/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-71269636607/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-13488783447/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3105927600271/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6215690152513/1000000000000:ℝ) := by nlinarith
  have hp1 : (10280611544759/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (514347926141/50000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-733147795713/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-693364714149/1000000000000:ℝ) := by nlinarith
  have hN : (422705449573/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (15253921628819/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (422705449573/250000000000:ℝ) (15253921628819/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2457325291/5000000000000:ℝ) ≤ ((422705449573/250000000000:ℝ)/(15253921628819/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_156 (x : ℝ) (h₁ : (32401/16384:ℝ) ≤ x) (h₂ : x ≤ (16203/8192:ℝ)) : (2518492283/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (347063153/5000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (703713687/10000000000:ℝ) := by nlinarith
  have hc1 : (997524954619/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (997524954619/1000000000000:ℝ) ≤ taylorCos (703713687/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (498795956361/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (347063153/5000000000:ℝ) + taylorErr ≤ (498795956361/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (69356902111/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (69356902111/1000000000000:ℝ) ≤ taylorSin (347063153/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (35156651993/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (703713687/10000000000:ℝ) + taylorErr ≤ (35156651993/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (997524954619/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (498795956361/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-35156651993/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-69356902111/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1242562787707/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (388360792283/62500000000:ℝ) := by nlinarith
  have hp1 : (10282198254777/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5141892551371/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-90385863507/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-356570708921/500000000000:ℝ) := by nlinarith
  have hN : (1710666372461/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (19055485437783/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1710666372461/1000000000000:ℝ) (19055485437783/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2518492283/5000000000000:ℝ) ≤ ((1710666372461/1000000000000:ℝ)/(19055485437783/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_157 (x : ℝ) (h₁ : (16203/8192:ℝ) ≤ x) (h₂ : x ≤ (32411/16384:ℝ)) : (4977151133/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (342269463/5000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (694126307/10000000000:ℝ) := by nlinarith
  have hc1 : (997591908191/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (997591908191/1000000000000:ℝ) ≤ taylorCos (694126307/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (997657949329/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (342269463/5000000000:ℝ) + taylorErr ≤ (997657949329/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (68400441109/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (68400441109/1000000000000:ℝ) ≤ taylorSin (342269463/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (13871381347/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (694126307/10000000000:ℝ) + taylorErr ≤ (13871381347/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (997591908191/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (997657949329/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-13871381347/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-68400441109/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6213772676527/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6214731414521/1000000000000:ℝ) := by nlinarith
  have hp1 : (5141892482397/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5142685906391/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-356680786777/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-351707713931/500000000000:ℝ) := by nlinarith
  have hN : (1701007336053/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (76245773109269/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1701007336053/1000000000000:ℝ) (76245773109269/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (4977151133/10000000000000:ℝ) ≤ ((1701007336053/1000000000000:ℝ)/(76245773109269/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_158 (x : ℝ) (h₁ : (16203/8192:ℝ) ≤ x) (h₂ : x ≤ (1013/512:ℝ)) : (2458339391/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (337475773/5000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (694126307/10000000000:ℝ) := by nlinarith
  have hc1 : (997591908191/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (997591908191/1000000000000:ℝ) ≤ taylorCos (694126307/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (997723068911/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (337475773/5000000000:ℝ) + taylorErr ≤ (997723068911/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (13488783447/200000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (13488783447/200000000000:ℝ) ≤ taylorSin (337475773/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (13871381347/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (694126307/10000000000:ℝ) + taylorErr ≤ (13871381347/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (997591908191/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (997723068911/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-13871381347/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-13488783447/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6213772676527/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6215690152513/1000000000000:ℝ) := by nlinarith
  have hp1 : (5141892482397/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (514347926141/50000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-142694324571/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-173394685507/250000000000:ℝ) := by nlinarith
  have hN : (1691170650219/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (15253921628819/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1691170650219/1000000000000:ℝ) (15253921628819/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2458339391/5000000000000:ℝ) ≤ ((1691170650219/1000000000000:ℝ)/(15253921628819/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_159 (x : ℝ) (h₁ : (32411/16384:ℝ) ≤ x) (h₂ : x ≤ (1013/512:ℝ)) : (61471063/125000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (337475773/5000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (684538927/10000000000:ℝ) := by nlinarith
  have hc1 : (498828972399/500000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (498828972399/500000000000:ℝ) ≤ taylorCos (684538927/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (997723068911/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (337475773/5000000000:ℝ) + taylorErr ≤ (997723068911/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (13488783447/200000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (13488783447/200000000000:ℝ) ≤ taylorSin (337475773/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (68400445733/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (684538927/10000000000:ℝ) + taylorErr ≤ (68400445733/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (498828972399/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (997723068911/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-68400445733/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-13488783447/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (155368285363/25000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6215690152513/1000000000000:ℝ) := by nlinarith
  have hp1 : (2571342918703/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (514347926141/50000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-351816274099/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-693685755967/1000000000000:ℝ) := by nlinarith
  have hN : (338268740153/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (15253921628819/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (338268740153/200000000000:ℝ) (15253921628819/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (61471063/125000000000:ℝ) ≤ ((338268740153/200000000000:ℝ)/(15253921628819/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_160 (x : ℝ) (h₁ : (1013/512:ℝ) ≤ x) (h₂ : x ≤ (32421/16384:ℝ)) : (60732327/125000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (332682083/5000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (674951547/10000000000:ℝ) := by nlinarith
  have hc1 : (49886153219/50000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (49886153219/50000000000:ℝ) ≤ taylorCos (674951547/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (997787271407/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (332682083/5000000000:ℝ) + taylorErr ≤ (997787271407/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (66487331367/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (66487331367/1000000000000:ℝ) ≤ taylorSin (332682083/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (67443921859/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (674951547/10000000000:ℝ) + taylorErr ≤ (67443921859/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (49886153219/50000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (997787271407/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-67443921859/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-66487331367/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (97120158633/15625000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3108324445253/500000000000:ℝ) := by nlinarith
  have hp1 : (10286958384829/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10288545232859/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-86737480091/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-68395241089/100000000000:ℝ) := by nlinarith
  have hN : (168167547527/100000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (76293446855659/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (168167547527/100000000000:ℝ) (76293446855659/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (60732327/125000000000:ℝ) ≤ ((168167547527/100000000000:ℝ)/(76293446855659/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_161 (x : ℝ) (h₁ : (1013/512:ℝ) ≤ x) (h₂ : x ≤ (16213/8192:ℝ)) : (1199722203/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (327888393/5000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (674951547/10000000000:ℝ) := by nlinarith
  have hc1 : (49886153219/50000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (49886153219/50000000000:ℝ) ≤ taylorCos (674951547/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (498925278379/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (327888393/5000000000:ℝ) + taylorErr ≤ (498925278379/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (32765342193/500000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (32765342193/500000000000:ℝ) ≤ taylorSin (327888393/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (67443921859/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (674951547/10000000000:ℝ) + taylorErr ≤ (67443921859/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (49886153219/50000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (498925278379/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-67443921859/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-32765342193/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (97120158633/15625000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3108803814249/500000000000:ℝ) := by nlinarith
  have hp1 : (10286958384829/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10290131942897/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-173501713669/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-84263927901/125000000000:ℝ) := by nlinarith
  have hN : (417958621897/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (38158644621957/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (417958621897/250000000000:ℝ) (38158644621957/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1199722203/2500000000000:ℝ) ≤ ((417958621897/250000000000:ℝ)/(38158644621957/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_162 (x : ℝ) (h₁ : (1013/512:ℝ) ≤ x) (h₂ : x ≤ (8109/4096:ℝ)) : (4680699447/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (318301013/5000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (674951547/10000000000:ℝ) := by nlinarith
  have hc1 : (49886153219/50000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (49886153219/50000000000:ℝ) ≤ taylorCos (674951547/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (199594875159/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (318301013/5000000000:ℝ) + taylorErr ≤ (199594875159/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (318086053/5000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (318086053/5000000000:ℝ) ≤ taylorSin (318301013/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (67443921859/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (674951547/10000000000:ℝ) + taylorErr ≤ (67443921859/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (49886153219/50000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (199594875159/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-67443921859/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-318086053/5000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (97120158633/15625000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6219525104483/1000000000000:ℝ) := by nlinarith
  have hp1 : (10286958384829/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (411732214519/40000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-173555220643/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-654427598001/1000000000000:ℝ) := by nlinarith
  have hN : (1652150662381/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (76364985050589/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1652150662381/1000000000000:ℝ) (76364985050589/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (4680699447/10000000000000:ℝ) ≤ ((1652150662381/1000000000000:ℝ)/(76364985050589/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_163 (x : ℝ) (h₁ : (1013/512:ℝ) ≤ x) (h₂ : x ≤ (4057/2048:ℝ)) : (2224562793/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (598252507/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (674951547/10000000000:ℝ) := by nlinarith
  have hc1 : (49886153219/50000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (49886153219/50000000000:ℝ) ≤ taylorCos (674951547/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (124776375703/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (598252507/10000000000:ℝ) + taylorErr ≤ (124776375703/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (59789568457/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (59789568457/1000000000000:ℝ) ≤ taylorSin (598252507/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (67443921859/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (674951547/10000000000:ℝ) + taylorErr ≤ (67443921859/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (49886153219/50000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (124776375703/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-67443921859/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-59789568457/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (97120158633/15625000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6223360056453/1000000000000:ℝ) := by nlinarith
  have hp1 : (10286958384829/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1029965220313/100000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-694648938363/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-153763200641/250000000000:ℝ) := by nlinarith
  have hN : (25199622921/15625000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (7646042078451/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (25199622921/15625000000:ℝ) (7646042078451/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2224562793/5000000000000:ℝ) ≤ ((25199622921/15625000000:ℝ)/(7646042078451/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_164 (x : ℝ) (h₁ : (1013/512:ℝ) ≤ x) (h₂ : x ≤ (2031/1024:ℝ)) : (200253263/500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (521553467/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (674951547/10000000000:ℝ) := by nlinarith
  have hc1 : (49886153219/50000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (49886153219/50000000000:ℝ) ≤ taylorCos (674951547/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (998640220447/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (521553467/10000000000:ℝ) + taylorErr ≤ (998640220447/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (5213170233/100000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (5213170233/100000000000:ℝ) ≤ taylorSin (521553467/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (67443921859/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (674951547/10000000000:ℝ) + taylorErr ≤ (67443921859/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (49886153219/50000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (998640220447/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-67443921859/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-5213170233/100000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (97120158633/15625000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (778878745049/125000000000:ℝ) := by nlinarith
  have hp1 : (10286958384829/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10312345883439/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-347752524973/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-536276652399/1000000000000:ℝ) := by nlinarith
  have hN : (1533999716779/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (38325734367303/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1533999716779/1000000000000:ℝ) (38325734367303/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (200253263/500000000000:ℝ) ≤ ((1533999716779/1000000000000:ℝ)/(38325734367303/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_165 (x : ℝ) (h₁ : (1013/512:ℝ) ≤ x) (h₂ : x ≤ (509/256:ℝ)) : (3192232409/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (368155389/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (674951547/10000000000:ℝ) := by nlinarith
  have hc1 : (49886153219/50000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (49886153219/50000000000:ℝ) ≤ taylorCos (674951547/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (999322386851/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (368155389/10000000000:ℝ) + taylorErr ≤ (999322386851/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (3680722067/100000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (3680722067/100000000000:ℝ) ≤ taylorSin (368155389/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (67443921859/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (674951547/10000000000:ℝ) + taylorErr ≤ (67443921859/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (49886153219/50000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999322386851/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-67443921859/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-3680722067/100000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (97120158633/15625000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6246369768271/1000000000000:ℝ) := by nlinarith
  have hp1 : (10286958384829/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5168866622029/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-87152159139/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-378634347293/1000000000000:ℝ) := by nlinarith
  have hN : (1376357411673/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (3851713528197/50000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1376357411673/1000000000000:ℝ) (3851713528197/50000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (3192232409/10000000000000:ℝ) ≤ ((1376357411673/1000000000000:ℝ)/(3851713528197/50000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_166 (x : ℝ) (h₁ : (32421/16384:ℝ) ≤ x) (h₂ : x ≤ (16213/8192:ℝ)) : (4799854363/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (327888393/5000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (665364167/10000000000:ℝ) := by nlinarith
  have hc1 : (249446816719/250000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (249446816719/250000000000:ℝ) ≤ taylorCos (665364167/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (498925278379/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (327888393/5000000000:ℝ) + taylorErr ≤ (498925278379/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (32765342193/500000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (32765342193/500000000000:ℝ) ≤ taylorSin (327888393/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (66487335991/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (665364167/10000000000:ℝ) + taylorErr ≤ (66487335991/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (249446816719/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (498925278379/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-66487335991/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-32765342193/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1243329778101/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3108803814249/500000000000:ℝ) := by nlinarith
  have hp1 : (10288545094847/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10290131942897/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-17104086497/25000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-674215401401/1000000000000:ℝ) := by nlinarith
  have hN : (1672002668277/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (38158644621957/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1672002668277/1000000000000:ℝ) (38158644621957/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (4799854363/10000000000000:ℝ) ≤ ((1672002668277/1000000000000:ℝ)/(38158644621957/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_167 (x : ℝ) (h₁ : (16213/8192:ℝ) ≤ x) (h₂ : x ≤ (32431/16384:ℝ)) : (2370744759/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (323094703/5000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (655776787/10000000000:ℝ) := by nlinarith
  have hc1 : (997850552227/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (997850552227/1000000000000:ℝ) ≤ taylorCos (655776787/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (498956462453/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (323094703/5000000000:ℝ) + taylorErr ≤ (498956462453/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (64573977171/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (64573977171/1000000000000:ℝ) ≤ taylorSin (323094703/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (6553068901/100000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (655776787/10000000000:ℝ) + taylorErr ≤ (6553068901/100000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (997850552227/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (498956462453/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-6553068901/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-64573977171/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6217607628497/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (621856636649/100000000000:ℝ) := by nlinarith
  have hp1 : (160783309451/15625000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2058343730587/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-84302926803/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-664474736253/1000000000000:ℝ) := by nlinarith
  have hN : (10389533053/6250000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (38170567654441/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (10389533053/6250000000:ℝ) (38170567654441/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2370744759/5000000000000:ℝ) ≤ ((10389533053/6250000000:ℝ)/(38170567654441/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_168 (x : ℝ) (h₁ : (16213/8192:ℝ) ≤ x) (h₂ : x ≤ (8109/4096:ℝ)) : (4682565917/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (318301013/5000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (655776787/10000000000:ℝ) := by nlinarith
  have hc1 : (997850552227/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (997850552227/1000000000000:ℝ) ≤ taylorCos (655776787/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (199594875159/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (318301013/5000000000:ℝ) + taylorErr ≤ (199594875159/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (318086053/5000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (318086053/5000000000:ℝ) ≤ taylorSin (318301013/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (6553068901/100000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (655776787/10000000000:ℝ) + taylorErr ≤ (6553068901/100000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (997850552227/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (199594875159/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-6553068901/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-318086053/5000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6217607628497/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6219525104483/1000000000000:ℝ) := by nlinarith
  have hp1 : (160783309451/15625000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (411732214519/40000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-674527392627/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-654629482131/1000000000000:ℝ) := by nlinarith
  have hN : (826240017179/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (76364985050589/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (826240017179/500000000000:ℝ) (76364985050589/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (4682565917/10000000000000:ℝ) ≤ ((826240017179/500000000000:ℝ)/(76364985050589/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_169 (x : ℝ) (h₁ : (32431/16384:ℝ) ≤ x) (h₂ : x ≤ (8109/4096:ℝ)) : (2341745747/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (318301013/5000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (646189407/10000000000:ℝ) := by nlinarith
  have hc1 : (124739115047/125000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (124739115047/125000000000:ℝ) ≤ taylorCos (646189407/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (199594875159/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (318301013/5000000000:ℝ) + taylorErr ≤ (199594875159/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (318086053/5000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (318086053/5000000000:ℝ) ≤ taylorSin (318301013/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (12914796359/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (646189407/10000000000:ℝ) + taylorErr ≤ (12914796359/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (124739115047/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (199594875159/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-12914796359/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-318086053/5000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6218566366489/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6219525104483/1000000000000:ℝ) := by nlinarith
  have hp1 : (10291718514881/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (411732214519/40000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-4154248207/6250000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-654730424197/1000000000000:ℝ) := by nlinarith
  have hN : (1652643344573/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (76364985050589/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1652643344573/1000000000000:ℝ) (76364985050589/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2341745747/5000000000000:ℝ) ≤ ((1652643344573/1000000000000:ℝ)/(76364985050589/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_170 (x : ℝ) (h₁ : (8109/4096:ℝ) ≤ x) (h₂ : x ≤ (32441/16384:ℝ)) : (2312930081/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (627014647/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (636602027/10000000000:ℝ) := by nlinarith
  have hc1 : (15593349551/15625000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (15593349551/15625000000:ℝ) ≤ taylorCos (636602027/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (12475436367/12500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (627014647/10000000000:ℝ) + taylorErr ≤ (12475436367/12500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (31330192827/500000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (31330192827/500000000000:ℝ) ≤ taylorSin (627014647/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (7952151903/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (636602027/10000000000:ℝ) + taylorErr ≤ (7952151903/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (15593349551/15625000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (12475436367/12500000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-7952151903/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-31330192827/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3109762552241/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (248819353699/40000000000:ℝ) := by nlinarith
  have hp1 : (10293305224899/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10294892073013/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-654932364717/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-322491237523/500000000000:ℝ) := by nlinarith
  have hN : (164295684631/100000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (38194419234493/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (164295684631/100000000000:ℝ) (38194419234493/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2312930081/5000000000000:ℝ) ≤ ((164295684631/100000000000:ℝ)/(38194419234493/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_171 (x : ℝ) (h₁ : (8109/4096:ℝ) ≤ x) (h₂ : x ≤ (16223/8192:ℝ)) : (4567709043/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (617427267/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (636602027/10000000000:ℝ) := by nlinarith
  have hc1 : (15593349551/15625000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (15593349551/15625000000:ℝ) ≤ taylorCos (636602027/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (24952363139/25000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (617427267/10000000000:ℝ) + taylorErr ≤ (24952363139/25000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (61703503011/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (61703503011/1000000000000:ℝ) ≤ taylorSin (617427267/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (7952151903/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (636602027/10000000000:ℝ) + taylorErr ≤ (7952151903/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (15593349551/15625000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (24952363139/25000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-7952151903/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-61703503011/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3109762552241/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1555360645117/250000000000:ℝ) := by nlinarith
  have hp1 : (10293305224899/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10296478783053/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-655033306791/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-635132989937/1000000000000:ℝ) := by nlinarith
  have hN : (1633107361201/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (76412695564121/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1633107361201/1000000000000:ℝ) (76412695564121/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (4567709043/10000000000000:ℝ) ≤ ((1633107361201/1000000000000:ℝ)/(76412695564121/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_172 (x : ℝ) (h₁ : (8109/4096:ℝ) ≤ x) (h₂ : x ≤ (4057/2048:ℝ)) : (4452606511/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (598252507/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (636602027/10000000000:ℝ) := by nlinarith
  have hc1 : (15593349551/15625000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (15593349551/15625000000:ℝ) ≤ taylorCos (636602027/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (124776375703/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (598252507/10000000000:ℝ) + taylorErr ≤ (124776375703/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (59789568457/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (59789568457/1000000000000:ℝ) ≤ taylorSin (598252507/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (7952151903/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (636602027/10000000000:ℝ) + taylorErr ≤ (7952151903/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (15593349551/15625000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (124776375703/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-7952151903/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-59789568457/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3109762552241/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6223360056453/1000000000000:ℝ) := by nlinarith
  have hp1 : (10293305224899/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1029965220313/100000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-655235190939/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-38464517337/62500000000:ℝ) := by nlinarith
  have hN : (100837915541/62500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (7646042078451/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (100837915541/62500000000:ℝ) (7646042078451/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (4452606511/10000000000000:ℝ) ≤ ((100837915541/62500000000:ℝ)/(7646042078451/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_173 (x : ℝ) (h₁ : (32441/16384:ℝ) ≤ x) (h₂ : x ≤ (16223/8192:ℝ)) : (4568595377/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (617427267/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (78376831/1250000000:ℝ) := by nlinarith
  have hc1 : (99803490483/100000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (99803490483/100000000000:ℝ) ≤ taylorCos (78376831/1250000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (24952363139/25000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (617427267/10000000000:ℝ) + taylorErr ≤ (24952363139/25000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (61703503011/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (61703503011/1000000000000:ℝ) ≤ taylorSin (617427267/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (31330195139/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (78376831/1250000000:ℝ) + taylorErr ≤ (31330195139/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (99803490483/100000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (24952363139/25000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-31330195139/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-61703503011/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3110241921237/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1555360645117/250000000000:ℝ) := by nlinarith
  have hp1 : (2573722983729/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10296478783053/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-161295344759/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-39701930969/62500000000:ℝ) := by nlinarith
  have hN : (816632900167/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (76412695564121/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (816632900167/500000000000:ℝ) (76412695564121/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (4568595377/10000000000000:ℝ) ≤ ((816632900167/500000000000:ℝ)/(76412695564121/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_174 (x : ℝ) (h₁ : (16223/8192:ℝ) ≤ x) (h₂ : x ≤ (32451/16384:ℝ)) : (4511697009/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (607839887/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (154356817/2500000000:ℝ) := by nlinarith
  have hc1 : (998094521029/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (998094521029/1000000000000:ℝ) ≤ taylorCos (154356817/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (998153224333/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (607839887/10000000000:ℝ) + taylorErr ≤ (998153224333/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (60746563653/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (60746563653/1000000000000:ℝ) ≤ taylorSin (607839887/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (15425876909/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (154356817/2500000000:ℝ) + taylorErr ≤ (15425876909/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (998094521029/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (998153224333/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-15425876909/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-60746563653/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6221442580467/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (311120065923/50000000000:ℝ) := by nlinarith
  have hp1 : (5148239322467/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10298065493091/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-635426762789/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-312737847703/500000000000:ℝ) := by nlinarith
  have hN : (324714043287/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (38218278167973/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (324714043287/200000000000:ℝ) (38218278167973/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (4511697009/10000000000000:ℝ) ≤ ((324714043287/200000000000:ℝ)/(38218278167973/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_175 (x : ℝ) (h₁ : (16223/8192:ℝ) ≤ x) (h₂ : x ≤ (4057/2048:ℝ)) : (44543171/100000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (598252507/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (154356817/2500000000:ℝ) := by nlinarith
  have hc1 : (998094521029/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (998094521029/1000000000000:ℝ) ≤ taylorCos (154356817/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (124776375703/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (598252507/10000000000:ℝ) + taylorErr ≤ (124776375703/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (59789568457/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (59789568457/1000000000000:ℝ) ≤ taylorSin (598252507/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (15425876909/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (154356817/2500000000:ℝ) + taylorErr ≤ (15425876909/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (998094521029/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (124776375703/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-15425876909/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-59789568457/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6221442580467/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6223360056453/1000000000000:ℝ) := by nlinarith
  have hp1 : (5148239322467/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1029965220313/100000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-158881167091/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-615622014807/1000000000000:ℝ) := by nlinarith
  have hN : (403429133959/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (7646042078451/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (403429133959/250000000000:ℝ) (7646042078451/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (44543171/100000000000:ℝ) ≤ ((403429133959/250000000000:ℝ)/(7646042078451/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_176 (x : ℝ) (h₁ : (32451/16384:ℝ) ≤ x) (h₂ : x ≤ (4057/2048:ℝ)) : (4455164921/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (598252507/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (37989993/625000000:ℝ) := by nlinarith
  have hc1 : (499076609901/500000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (499076609901/500000000000:ℝ) ≤ taylorCos (37989993/625000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (124776375703/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (598252507/10000000000:ℝ) + taylorErr ≤ (124776375703/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (59789568457/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (59789568457/1000000000000:ℝ) ≤ taylorSin (598252507/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (60746568277/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (37989993/625000000:ℝ) + taylorErr ≤ (60746568277/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (499076609901/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (124776375703/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-60746568277/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-59789568457/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6222401318459/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6223360056453/1000000000000:ℝ) := by nlinarith
  have hp1 : (10298065354951/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1029965220313/100000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-625668525787/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-307858441757/500000000000:ℝ) := by nlinarith
  have hN : (403467525829/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (7646042078451/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (403467525829/250000000000:ℝ) (7646042078451/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (4455164921/10000000000000:ℝ) ≤ ((403467525829/250000000000:ℝ)/(7646042078451/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_177 (x : ℝ) (h₁ : (4057/2048:ℝ) ≤ x) (h₂ : x ≤ (32461/16384:ℝ)) : (175959959/400000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (588665127/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (149563127/2500000000:ℝ) := by nlinarith
  have hc1 : (499105500547/500000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (499105500547/500000000000:ℝ) ≤ taylorCos (149563127/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (499133934691/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (588665127/10000000000:ℝ) + taylorErr ≤ (499133934691/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (1838516197/31250000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (1838516197/31250000000:ℝ) ≤ taylorSin (588665127/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (59789573081/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (149563127/2500000000:ℝ) + taylorErr ≤ (59789573081/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (499105500547/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (499133934691/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-59789573081/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-1838516197/31250000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1555840014113/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1244863758889/200000000000:ℝ) := by nlinarith
  have hp1 : (10299652064969/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (643827432073/62500000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-76988334603/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-605954468637/1000000000000:ℝ) := by nlinarith
  have hN : (1604165469731/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (76484288909763/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1604165469731/1000000000000:ℝ) (76484288909763/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (175959959/400000000000:ℝ) ≤ ((1604165469731/1000000000000:ℝ)/(76484288909763/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_178 (x : ℝ) (h₁ : (4057/2048:ℝ) ≤ x) (h₂ : x ≤ (16233/8192:ℝ)) : (2171194499/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (579077747/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (149563127/2500000000:ℝ) := by nlinarith
  have hc1 : (499105500547/500000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (499105500547/500000000000:ℝ) ≤ taylorCos (149563127/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (998323815553/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (579077747/10000000000:ℝ) + taylorErr ≤ (998323815553/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (57875414073/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (57875414073/1000000000000:ℝ) ≤ taylorSin (579077747/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (59789573081/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (149563127/2500000000:ℝ) + taylorErr ≤ (59789573081/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (499105500547/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (998323815553/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-59789573081/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-57875414073/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1555840014113/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6225277532437/1000000000000:ℝ) := by nlinarith
  have hp1 : (10299652064969/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5151412811603/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-30800077277/50000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-596096628067/1000000000000:ℝ) := by nlinarith
  have hN : (1594307629161/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (7650816071173/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1594307629161/1000000000000:ℝ) (7650816071173/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2171194499/5000000000000:ℝ) ≤ ((1594307629161/1000000000000:ℝ)/(7650816071173/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_179 (x : ℝ) (h₁ : (4057/2048:ℝ) ≤ x) (h₂ : x ≤ (8119/4096:ℝ)) : (1057590771/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (559902987/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (149563127/2500000000:ℝ) := by nlinarith
  have hc1 : (499105500547/500000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (499105500547/500000000000:ℝ) ≤ taylorCos (149563127/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (249608238733/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (559902987/10000000000:ℝ) + taylorErr ≤ (249608238733/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (55961046899/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (55961046899/1000000000000:ℝ) ≤ taylorSin (559902987/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (59789573081/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (149563127/2500000000:ℝ) + taylorErr ≤ (59789573081/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (499105500547/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (249608238733/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-59789573081/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-55961046899/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1555840014113/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3113597504211/500000000000:ℝ) := by nlinarith
  have hp1 : (10299652064969/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2576499760821/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-154047820743/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-576379312251/1000000000000:ℝ) := by nlinarith
  have hN : (314918062669/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (9569489418229/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (314918062669/200000000000:ℝ) (9569489418229/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1057590771/2500000000000:ℝ) ≤ ((314918062669/200000000000:ℝ)/(9569489418229/125000000000:ℝ))^2 := by norm_num
  linarith

end Zeta23Ext.Bridge.FourPoint
