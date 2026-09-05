import FourPoint.Base

noncomputable section
open Real
namespace Zeta23Ext.Bridge.FourPoint


theorem wc_1200 (x : ℝ) (h₁ : (1061/256:ℝ) ≤ x) (h₂ : x ≤ (17/4:ℝ)) : (5787071159/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1135145783/2500000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (449337233981/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1135145783/2500000000:ℝ) + taylorErr ≤ (449337233981/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (54827029533/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (54827029533/125000000000:ℝ) ≤ taylorSin (1135145783/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (176776695861/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/5000000000:ℝ) + taylorErr ≤ (176776695861/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (449337233981/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (54827029533/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (176776695861/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (13020428927573/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (13351768777757/1000000000000:ℝ) := by nlinarith
  have hp1 : (336699865693/15625000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (11048579341389/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4725824890907/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (15625050799431/1000000000000:ℝ) := by nlinarith
  have hN : (2138243828463/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (177769729494687/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2138243828463/250000000000:ℝ) (177769729494687/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (5787071159/10000000000000:ℝ) ≤ ((2138243828463/250000000000:ℝ)/(177769729494687/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1201 (x : ℝ) (h₁ : (267/64:ℝ) ≤ x) (h₂ : x ≤ (17/4:ℝ)) : (8382305677/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (5399612373/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (21443215307/25000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (5399612373/10000000000:ℝ) + taylorErr ≤ (21443215307/25000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (5141027419/10000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (5141027419/10000000000:ℝ) ≤ taylorSin (5399612373/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (176776695861/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/5000000000:ℝ) + taylorErr ≤ (176776695861/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (21443215307/25000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (5141027419/10000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (176776695861/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6553165925847/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (13351768777757/1000000000000:ℝ) := by nlinarith
  have hp1 : (21690960621911/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (11048579341389/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (11151382330169/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (15625050799431/1000000000000:ℝ) := by nlinarith
  have hN : (10293653717889/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (177769729494687/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (10293653717889/1000000000000:ℝ) (177769729494687/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (8382305677/10000000000000:ℝ) ≤ ((10293653717889/1000000000000:ℝ)/(177769729494687/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1202 (x : ℝ) (h₁ : (17/4:ℝ) ≤ x) (h₂ : x ≤ (549/128:ℝ)) : (16970875159/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (6626797003/10000000000:ℝ) ≤ Real.pi * ((9/2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((9/2:ℝ) - x) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * ((9/2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((9/2:ℝ) - x)) ≤ (157669285983/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (6626797003/10000000000:ℝ) + taylorErr ≤ (157669285983/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (123046317653/200000000000:ℝ) ≤ Real.sin (Real.pi * ((9/2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (123046317653/200000000000:ℝ) ≤ taylorSin (6626797003/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((9/2:ℝ) - x)) ≤ (176776695861/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/5000000000:ℝ) + taylorErr ≤ (176776695861/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * ((9/2:ℝ) - x)) := by
    have h := (trig_shift (9/2:ℝ) (x - (9/2:ℝ))).1
    rw [show (9/2:ℝ) + (x - (9/2:ℝ)) = x by ring, cs_h9.1, cs_h9.2] at h
    rw [h, cos_flip (9/2:ℝ) x, sin_flip (9/2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((9/2:ℝ) - x)) := by
    have h := (trig_shift (9/2:ℝ) (x - (9/2:ℝ))).2
    rw [show (9/2:ℝ) + (x - (9/2:ℝ)) = x by ring, cs_h9.1, cs_h9.2] at h
    rw [h, cos_flip (9/2:ℝ) x, sin_flip (9/2:ℝ) x]; ring
  have hcxl : (123046317653/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (176776695861/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (88388347351/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (157669285983/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3337942194439/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3368621810197/250000000000:ℝ) := by nlinarith
  have hp1 : (11048579193183/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (22300257567731/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (15625050487393/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (8790164219853/500000000000:ℝ) := by nlinarith
  have hN : (14917943703949/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (181061806402159/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (14917943703949/1000000000000:ℝ) (181061806402159/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (16970875159/10000000000000:ℝ) ≤ ((14917943703949/1000000000000:ℝ)/(181061806402159/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1203 (x : ℝ) (h₁ : (17/4:ℝ) ≤ x) (h₂ : x ≤ (1101/256:ℝ)) : (8393078289/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (3129320807/5000000000:ℝ) ≤ Real.pi * ((9/2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((9/2:ℝ) - x) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * ((9/2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((9/2:ℝ) - x)) ≤ (810457200541/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (3129320807/5000000000:ℝ) + taylorErr ≤ (810457200541/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (585797855147/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((9/2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (585797855147/1000000000000:ℝ) ≤ taylorSin (3129320807/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((9/2:ℝ) - x)) ≤ (176776695861/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/5000000000:ℝ) + taylorErr ≤ (176776695861/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * ((9/2:ℝ) - x)) := by
    have h := (trig_shift (9/2:ℝ) (x - (9/2:ℝ))).1
    rw [show (9/2:ℝ) + (x - (9/2:ℝ)) = x by ring, cs_h9.1, cs_h9.2] at h
    rw [h, cos_flip (9/2:ℝ) x, sin_flip (9/2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((9/2:ℝ) - x)) := by
    have h := (trig_shift (9/2:ℝ) (x - (9/2:ℝ))).2
    rw [show (9/2:ℝ) + (x - (9/2:ℝ)) = x by ring, cs_h9.1, cs_h9.2] at h
    rw [h, cos_flip (9/2:ℝ) x, sin_flip (9/2:ℝ) x]; ring
  have hcxl : (585797855147/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (176776695861/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (88388347351/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (810457200541/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3337942194439/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (13511302779697/1000000000000:ℝ) := by nlinarith
  have hp1 : (11048579193183/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (349393550519/15625000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (15625050487393/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (9061392602903/500000000000:ℝ) := by nlinarith
  have hN : (14917943703949/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (22756912850581/62500000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (14917943703949/1000000000000:ℝ) (22756912850581/62500000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (8393078289/5000000000000:ℝ) ≤ ((14917943703949/1000000000000:ℝ)/(22756912850581/62500000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1204 (x : ℝ) (h₁ : (17/4:ℝ) ≤ x) (h₂ : x ≤ (277/64:ℝ)) : (16364828489/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (5399612373/10000000000:ℝ) ≤ Real.pi * ((9/2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((9/2:ℝ) - x) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * ((9/2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((9/2:ℝ) - x)) ≤ (21443215307/25000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (5399612373/10000000000:ℝ) + taylorErr ≤ (21443215307/25000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (5141027419/10000000000:ℝ) ≤ Real.sin (Real.pi * ((9/2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (5141027419/10000000000:ℝ) ≤ taylorSin (5399612373/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((9/2:ℝ) - x)) ≤ (176776695861/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/5000000000:ℝ) + taylorErr ≤ (176776695861/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * ((9/2:ℝ) - x)) := by
    have h := (trig_shift (9/2:ℝ) (x - (9/2:ℝ))).1
    rw [show (9/2:ℝ) + (x - (9/2:ℝ)) = x by ring, cs_h9.1, cs_h9.2] at h
    rw [h, cos_flip (9/2:ℝ) x, sin_flip (9/2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((9/2:ℝ) - x)) := by
    have h := (trig_shift (9/2:ℝ) (x - (9/2:ℝ))).2
    rw [show (9/2:ℝ) + (x - (9/2:ℝ)) = x by ring, cs_h9.1, cs_h9.2] at h
    rw [h, cos_flip (9/2:ℝ) x, sin_flip (9/2:ℝ) x]; ring
  have hcxl : (5141027419/10000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (176776695861/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (88388347351/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (21443215307/25000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3337942194439/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (13597205703819/1000000000000:ℝ) := by nlinarith
  have hp1 : (11048579193183/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (22503356452683/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (15625050487393/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (9650886350901/500000000000:ℝ) := by nlinarith
  have hN : (14917943703949/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (5762000092249/15625000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (14917943703949/1000000000000:ℝ) (5762000092249/15625000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (16364828489/10000000000000:ℝ) ≤ ((14917943703949/1000000000000:ℝ)/(5762000092249/15625000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1205 (x : ℝ) (h₁ : (17/4:ℝ) ≤ x) (h₂ : x ≤ (141/32:ℝ)) : (15231803251/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (368155389/1250000000:ℝ) ≤ Real.pi * ((9/2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((9/2:ℝ) - x) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * ((9/2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((9/2:ℝ) - x)) ≤ (29904385563/31250000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (368155389/1250000000:ℝ) + taylorErr ≤ (29904385563/31250000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (290284674921/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((9/2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (290284674921/1000000000000:ℝ) ≤ taylorSin (368155389/1250000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((9/2:ℝ) - x)) ≤ (176776695861/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/5000000000:ℝ) + taylorErr ≤ (176776695861/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * ((9/2:ℝ) - x)) := by
    have h := (trig_shift (9/2:ℝ) (x - (9/2:ℝ))).1
    rw [show (9/2:ℝ) + (x - (9/2:ℝ)) = x by ring, cs_h9.1, cs_h9.2] at h
    rw [h, cos_flip (9/2:ℝ) x, sin_flip (9/2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((9/2:ℝ) - x)) := by
    have h := (trig_shift (9/2:ℝ) (x - (9/2:ℝ))).2
    rw [show (9/2:ℝ) + (x - (9/2:ℝ)) = x by ring, cs_h9.1, cs_h9.2] at h
    rw [h, cos_flip (9/2:ℝ) x, sin_flip (9/2:ℝ) x]; ring
  have hcxl : (290284674921/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (176776695861/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (88388347351/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (29904385563/31250000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3337942194439/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (13842642629881/1000000000000:ℝ) := by nlinarith
  have hp1 : (11048579193183/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (22909554222587/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (15625050487393/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (21923076561559/1000000000000:ℝ) := by nlinarith
  have hN : (14917943703949/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (191118754978599/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (14917943703949/1000000000000:ℝ) (191118754978599/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (15231803251/10000000000000:ℝ) ≤ ((14917943703949/1000000000000:ℝ)/(191118754978599/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1206 (x : ℝ) (h₁ : (17/4:ℝ) ≤ x) (h₂ : x ≤ (283/64:ℝ)) : (7508548427/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/500000000:ℝ) ≤ Real.pi * ((9/2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((9/2:ℝ) - x) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * ((9/2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((9/2:ℝ) - x)) ≤ (60626953467/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/500000000:ℝ) + taylorErr ≤ (60626953467/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (242980177581/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((9/2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (242980177581/1000000000000:ℝ) ≤ taylorSin (122718463/500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((9/2:ℝ) - x)) ≤ (176776695861/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/5000000000:ℝ) + taylorErr ≤ (176776695861/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * ((9/2:ℝ) - x)) := by
    have h := (trig_shift (9/2:ℝ) (x - (9/2:ℝ))).1
    rw [show (9/2:ℝ) + (x - (9/2:ℝ)) = x by ring, cs_h9.1, cs_h9.2] at h
    rw [h, cos_flip (9/2:ℝ) x, sin_flip (9/2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((9/2:ℝ) - x)) := by
    have h := (trig_shift (9/2:ℝ) (x - (9/2:ℝ))).2
    rw [show (9/2:ℝ) + (x - (9/2:ℝ)) = x by ring, cs_h9.1, cs_h9.2] at h
    rw [h, cos_flip (9/2:ℝ) x, sin_flip (9/2:ℝ) x]; ring
  have hcxl : (242980177581/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (176776695861/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (88388347351/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (60626953467/62500000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3337942194439/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (13891730015093/1000000000000:ℝ) := by nlinarith
  have hp1 : (11048579193183/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2873849222071/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (15625050487393/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (22301788551383/1000000000000:ℝ) := by nlinarith
  have hN : (14917943703949/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (48120040703059/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (14917943703949/1000000000000:ℝ) (48120040703059/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (7508548427/5000000000000:ℝ) ≤ ((14917943703949/1000000000000:ℝ)/(48120040703059/125000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1207 (x : ℝ) (h₁ : (17/4:ℝ) ≤ x) (h₂ : x ≤ (287/64:ℝ)) : (7097602747/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/2500000000:ℝ) ≤ Real.pi * ((9/2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((9/2:ℝ) - x) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * ((9/2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((9/2:ℝ) - x)) ≤ (249698864617/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/2500000000:ℝ) + taylorErr ≤ (249698864617/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (49067672053/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((9/2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (49067672053/1000000000000:ℝ) ≤ taylorSin (122718463/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((9/2:ℝ) - x)) ≤ (176776695861/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/5000000000:ℝ) + taylorErr ≤ (176776695861/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * ((9/2:ℝ) - x)) := by
    have h := (trig_shift (9/2:ℝ) (x - (9/2:ℝ))).1
    rw [show (9/2:ℝ) + (x - (9/2:ℝ)) = x by ring, cs_h9.1, cs_h9.2] at h
    rw [h, cos_flip (9/2:ℝ) x, sin_flip (9/2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((9/2:ℝ) - x)) := by
    have h := (trig_shift (9/2:ℝ) (x - (9/2:ℝ))).2
    rw [show (9/2:ℝ) + (x - (9/2:ℝ)) = x by ring, cs_h9.1, cs_h9.2] at h
    rw [h, cos_flip (9/2:ℝ) x, sin_flip (9/2:ℝ) x]; ring
  have hcxl : (49067672053/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (176776695861/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (88388347351/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (249698864617/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3337942194439/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (7044039777971/500000000000:ℝ) := by nlinarith
  have hp1 : (11048579193183/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2331575199249/100000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (15625050487393/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (11643833600433/500000000000:ℝ) := by nlinarith
  have hN : (14917943703949/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (197973985574551/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (14917943703949/1000000000000:ℝ) (197973985574551/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (7097602747/5000000000000:ℝ) ≤ ((14917943703949/1000000000000:ℝ)/(197973985574551/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1208 (x : ℝ) (h₁ : (75/16:ℝ) ≤ x) (h₂ : x ≤ (19/4:ℝ)) : (16026017701/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (235619449/400000000:ℝ) ≤ Real.pi * (x - (9/2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (9/2:ℝ)) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (9/2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (9/2:ℝ))) ≤ (207867403647/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (235619449/400000000:ℝ) + taylorErr ≤ (207867403647/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (555570230717/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (9/2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (555570230717/1000000000000:ℝ) ≤ taylorSin (235619449/400000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (9/2:ℝ))) ≤ (176776695861/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/5000000000:ℝ) + taylorErr ≤ (176776695861/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (9/2:ℝ))) := by
    have h := (trig_shift (9/2:ℝ) (x - (9/2:ℝ))).1
    rw [show (9/2:ℝ) + (x - (9/2:ℝ)) = x by ring, cs_h9.1, cs_h9.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (9/2:ℝ))) := by
    have h := (trig_shift (9/2:ℝ) (x - (9/2:ℝ))).2
    rw [show (9/2:ℝ) + (x - (9/2:ℝ)) = x by ring, cs_h9.1, cs_h9.2] at h
    rw [h]; ring
  have hcxl : (-176776695861/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-555570230717/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (88388347351/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (207867403647/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7363107781851/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1865320638069/125000000000:ℝ) := by nlinarith
  have hp1 : (24371865867317/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (6174206102541/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (17233511566979/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (20534659073867/1000000000000:ℝ) := by nlinarith
  have hN : (277954403089/15625000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (444365898599187/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (277954403089/15625000000:ℝ) (444365898599187/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (16026017701/10000000000000:ℝ) ≤ ((277954403089/15625000000:ℝ)/(444365898599187/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1209 (x : ℝ) (h₁ : (19/4:ℝ) ≤ x) (h₂ : x ≤ (1271/256:ℝ)) : (498772193/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1104466167/10000000000:ℝ) ≤ Real.pi * ((5:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((5:ℝ) - x) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * ((5:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((5:ℝ) - x)) ≤ (248476743067/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1104466167/10000000000:ℝ) + taylorErr ≤ (248476743067/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (27555551251/250000000000:ℝ) ≤ Real.sin (Real.pi * ((5:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (27555551251/250000000000:ℝ) ≤ taylorSin (1104466167/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((5:ℝ) - x)) ≤ (176776695861/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/5000000000:ℝ) + taylorErr ≤ (176776695861/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((5:ℝ) - x)) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h, cos_flip (5:ℝ) x, sin_flip (5:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * ((5:ℝ) - x)) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h, cos_flip (5:ℝ) x, sin_flip (5:ℝ) x]; ring
  have hcxl : (-248476743067/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-88388347351/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (27555551251/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (176776695861/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (14922565104551/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (7798758325611/500000000000:ℝ) := by nlinarith
  have hp1 : (24696824078881/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (25813868277401/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (272213840657/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (18253161365881/1000000000000:ℝ) := by nlinarith
  have hN : (1714622592689/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (60695631421287/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1714622592689/500000000000:ℝ) (60695631421287/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (498772193/10000000000000:ℝ) ≤ ((1714622592689/500000000000:ℝ)/(60695631421287/125000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1210 (x : ℝ) (h₁ : (19/4:ℝ) ≤ x) (h₂ : x ≤ (25479/5120:ℝ)) : (270897677/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (742446701/10000000000:ℝ) ≤ Real.pi * ((5:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((5:ℝ) - x) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * ((5:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((5:ℝ) - x)) ≤ (498622566279/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (742446701/10000000000:ℝ) + taylorErr ≤ (498622566279/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (74176477177/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((5:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (74176477177/1000000000000:ℝ) ≤ taylorSin (742446701/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((5:ℝ) - x)) ≤ (176776695861/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/5000000000:ℝ) + taylorErr ≤ (176776695861/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((5:ℝ) - x)) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h, cos_flip (5:ℝ) x, sin_flip (5:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * ((5:ℝ) - x)) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h, cos_flip (5:ℝ) x, sin_flip (5:ℝ) x]; ring
  have hcxl : (-498622566279/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-88388347351/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (74176477177/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (176776695861/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (14922565104551/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1954214824727/125000000000:ℝ) := by nlinarith
  have hp1 : (24696824078881/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (25873782448461/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1831923407631/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (9147763541331/500000000000:ℝ) := by nlinarith
  have hN : (2539030186439/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (121956578597849/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2539030186439/1000000000000:ℝ) (121956578597849/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (270897677/10000000000000:ℝ) ≤ ((2539030186439/1000000000000:ℝ)/(121956578597849/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1211 (x : ℝ) (h₁ : (1231/256:ℝ) ≤ x) (h₂ : x ≤ (5:ℝ)) : (14017409/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * ((5:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((5:ℝ) - x) ≤ (6013204689/10000000000:ℝ) := by nlinarith
  have hc1 : (824589300491/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((5:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (824589300491/1000000000000:ℝ) ≤ taylorCos (6013204689/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((5:ℝ) - x)) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * ((5:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((5:ℝ) - x)) ≤ (282865906543/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (6013204689/10000000000:ℝ) + taylorErr ≤ (282865906543/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((5:ℝ) - x)) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h, cos_flip (5:ℝ) x, sin_flip (5:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * ((5:ℝ) - x)) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h, cos_flip (5:ℝ) x, sin_flip (5:ℝ) x]; ring
  have hcxl : (-500000001131/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-824589300491/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (282865906543/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15106642799097/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15707963267949/1000000000000:ℝ) := by nlinarith
  have hp1 : (12500736201111/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (25387360619/976562500:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-11761/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (7353568026857/500000000000:ℝ) := by nlinarith
  have hN : (412294620843/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (492480220054471/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (412294620843/500000000000:ℝ) (492480220054471/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (14017409/5000000000000:ℝ) ≤ ((412294620843/500000000000:ℝ)/(492480220054471/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1212 (x : ℝ) (h₁ : (5:ℝ) ≤ x) (h₂ : x ≤ (641/128:ℝ)) : (533121/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (245436927/10000000000:ℝ) := by nlinarith
  have hc1 : (62481176027/62500000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (62481176027/62500000000:ℝ) ≤ taylorCos (245436927/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (24541230879/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (245436927/10000000000:ℝ) + taylorErr ≤ (24541230879/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-500000001131/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-62481176027/62500000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-24541230879/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1131/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3926990816987/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3933126740139/250000000000:ℝ) := by nlinarith
  have hp1 : (25996656925137/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (813664907839/31250000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-319493413783/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (58897/1000000000000:ℝ) := by nlinarith
  have hN : (180355994433/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (247011775263943/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (180355994433/500000000000:ℝ) (247011775263943/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (533121/1000000000000:ℝ) ≤ ((180355994433/500000000000:ℝ)/(247011775263943/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1213 (x : ℝ) (h₁ : (5135/1024:ℝ) ≤ x) (h₂ : x ≤ (10341/2048:ℝ)) : (796707/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (115048559/2500000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (387330149/2500000000:ℝ) := by nlinarith
  have hc1 : (494011007439/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (494011007439/500000000000:ℝ) ≤ taylorCos (387330149/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (998941295451/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (115048559/2500000000:ℝ) + taylorErr ≤ (998941295451/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (5750397479/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (5750397479/125000000000:ℝ) ≤ taylorSin (115048559/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (77156487649/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (387330149/2500000000:ℝ) + taylorErr ≤ (77156487649/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-998941295451/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-494011007439/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-77156487649/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-5750397479/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3150796538317/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (7931447663763/500000000000:ℝ) := by nlinarith
  have hp1 : (26072819005973/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26253069616109/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-126599665099/31250000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-599716290729/500000000000:ℝ) := by nlinarith
  have hN : (200491286007/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (502262896344093/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (200491286007/1000000000000:ℝ) (502262896344093/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (796707/5000000000000:ℝ) ≤ ((200491286007/1000000000000:ℝ)/(502262896344093/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1214 (x : ℝ) (h₁ : (5135/1024:ℝ) ≤ x) (h₂ : x ≤ (10361/2048:ℝ)) : (790561/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (115048559/2500000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (928058377/5000000000:ℝ) := by nlinarith
  have hc1 : (245705887231/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (245705887231/250000000000:ℝ) ≤ taylorCos (928058377/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (998941295451/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (115048559/2500000000:ℝ) + taylorErr ≤ (998941295451/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (5750397479/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (5750397479/125000000000:ℝ) ≤ taylorSin (115048559/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (36909547853/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (928058377/5000000000:ℝ) + taylorErr ≤ (36909547853/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-998941295451/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-245705887231/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-36909547853/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-5750397479/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3150796538317/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3973393735821/250000000000:ℝ) := by nlinarith
  have hp1 : (26072819005973/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26303844337347/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1213578751609/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-599716290729/500000000000:ℝ) := by nlinarith
  have hN : (200491286007/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (504211448955571/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (200491286007/1000000000000:ℝ) (504211448955571/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (790561/5000000000000:ℝ) ≤ ((200491286007/1000000000000:ℝ)/(504211448955571/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1215 (x : ℝ) (h₁ : (5135/1024:ℝ) ≤ x) (h₂ : x ≤ (2603/512:ℝ)) : (155031/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (115048559/2500000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (659611739/2500000000:ℝ) := by nlinarith
  have hc1 : (482697219707/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (482697219707/500000000000:ℝ) ≤ taylorCos (659611739/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (998941295451/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (115048559/2500000000:ℝ) + taylorErr ≤ (998941295451/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (5750397479/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (5750397479/125000000000:ℝ) ≤ taylorSin (115048559/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (130397060129/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (659611739/2500000000:ℝ) + taylorErr ≤ (130397060129/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-998941295451/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-482697219707/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-130397060129/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-5750397479/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3150796538317/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (7985903981733/500000000000:ℝ) := by nlinarith
  have hp1 : (26072819005973/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3304164984563/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1723413600673/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-599716290729/500000000000:ℝ) := by nlinarith
  have hN : (200491286007/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (63649662405459/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (200491286007/1000000000000:ℝ) (63649662405459/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (155031/1000000000000:ℝ) ≤ ((200491286007/1000000000000:ℝ)/(63649662405459/125000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1216 (x : ℝ) (h₁ : (10279/2048:ℝ) ≤ x) (h₂ : x ≤ (20669/4096:ℝ)) : (12553451/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (598252507/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (289922369/2000000000:ℝ) := by nlinarith
  have hc1 : (989511511411/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (989511511411/1000000000000:ℝ) ≤ taylorCos (289922369/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (124776375703/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (598252507/10000000000:ℝ) + taylorErr ≤ (124776375703/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (59789568457/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (59789568457/1000000000000:ℝ) ≤ taylorSin (598252507/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (144454023697/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (289922369/2000000000:ℝ) + taylorErr ≤ (144454023697/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-124776375703/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-989511511411/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-144454023697/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-59789568457/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3941947129669/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3170584890481/200000000000:ℝ) := by nlinarith
  have hp1 : (26095667630223/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26236567831707/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-378997779129/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-48757772069/31250000000:ℝ) := by nlinarith
  have hN : (70254712573/125000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (501630427387321/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (70254712573/125000000000:ℝ) (501630427387321/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (12553451/10000000000000:ℝ) ≤ ((70254712573/125000000000:ℝ)/(501630427387321/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1217 (x : ℝ) (h₁ : (1285/256:ℝ) ≤ x) (h₂ : x ≤ (645/128:ℝ)) : (14495053/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/2000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1227184631/10000000000:ℝ) := by nlinarith
  have hc1 : (124059941541/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (124059941541/125000000000:ℝ) ≤ taylorCos (1227184631/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (998118115163/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/2000000000:ℝ) + taylorErr ≤ (998118115163/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (2452829361/40000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (2452829361/40000000000:ℝ) ≤ taylorSin (122718463/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (12241067753/100000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1227184631/10000000000:ℝ) + taylorErr ≤ (12241067753/100000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-998118115163/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-124059941541/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-12241067753/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-2452829361/40000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1971165312433/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (791534086549/50000000000:ℝ) := by nlinarith
  have hp1 : (6524551591563/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3274969519851/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-3207129902521/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-800180585557/500000000000:ℝ) := by nlinarith
  have hN : (602243055951/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (976994078389/1953125000:ℝ) := by nlinarith
  have hfin := wfun_ge x (602243055951/1000000000000:ℝ) (976994078389/1953125000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (14495053/10000000000000:ℝ) ≤ ((602243055951/1000000000000:ℝ)/(976994078389/1953125000:ℝ))^2 := by norm_num
  linarith

theorem wc_1218 (x : ℝ) (h₁ : (1285/256:ℝ) ≤ x) (h₂ : x ≤ (5165/1024:ℝ)) : (2887779/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/2000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (138058271/1000000000:ℝ) := by nlinarith
  have hc1 : (495242540991/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (495242540991/500000000000:ℝ) ≤ taylorCos (138058271/1000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (998118115163/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/2000000000:ℝ) + taylorErr ≤ (998118115163/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (2452829361/40000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (2452829361/40000000000:ℝ) ≤ taylorSin (122718463/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (68810061969/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (138058271/1000000000:ℝ) + taylorErr ≤ (68810061969/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-998118115163/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-495242540991/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-68810061969/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-2452829361/40000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1971165312433/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15846021538859/1000000000000:ℝ) := by nlinarith
  have hp1 : (6524551591563/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (6556285879857/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-902276875359/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-800180585557/500000000000:ℝ) := by nlinarith
  have hN : (602243055951/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (501192797219967/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (602243055951/1000000000000:ℝ) (501192797219967/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2887779/2000000000000:ℝ) ≤ ((602243055951/1000000000000:ℝ)/(501192797219967/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1219 (x : ℝ) (h₁ : (1285/256:ℝ) ≤ x) (h₂ : x ≤ (2585/512:ℝ)) : (449469/312500000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/2000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (383495197/2500000000:ℝ) := by nlinarith
  have hc1 : (988257565467/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (988257565467/1000000000000:ℝ) ≤ taylorCos (383495197/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (998118115163/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/2000000000:ℝ) + taylorErr ≤ (998118115163/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (2452829361/40000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (2452829361/40000000000:ℝ) ≤ taylorSin (122718463/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (38199296883/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (383495197/2500000000:ℝ) + taylorErr ≤ (38199296883/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-998118115163/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-988257565467/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-38199296883/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-2452829361/40000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1971165312433/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (7930680673369/500000000000:ℝ) := by nlinarith
  have hp1 : (6524551591563/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26250530880047/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2005503644847/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-800180585557/500000000000:ℝ) := by nlinarith
  have hN : (602243055951/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (502165567543589/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (602243055951/1000000000000:ℝ) (502165567543589/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (449469/312500000000:ℝ) ≤ ((602243055951/1000000000000:ℝ)/(502165567543589/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1220 (x : ℝ) (h₁ : (1285/256:ℝ) ≤ x) (h₂ : x ≤ (1295/256:ℝ)) : (3568011/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/2000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (920388473/5000000000:ℝ) := by nlinarith
  have hc1 : (983105485159/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (983105485159/1000000000000:ℝ) ≤ taylorCos (920388473/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (998118115163/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/2000000000:ℝ) + taylorErr ≤ (998118115163/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (2452829361/40000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (2452829361/40000000000:ℝ) ≤ taylorSin (122718463/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (18303989027/100000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (920388473/5000000000:ℝ) + taylorErr ≤ (18303989027/100000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-998118115163/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-983105485159/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-18303989027/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-2452829361/40000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1971165312433/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (248313140039/15625000000:ℝ) := by nlinarith
  have hp1 : (6524551591563/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5260261120257/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-4814188091217/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-800180585557/500000000000:ℝ) := by nlinarith
  have hN : (602243055951/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (252056965953651/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (602243055951/1000000000000:ℝ) (252056965953651/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (3568011/2500000000000:ℝ) ≤ ((602243055951/1000000000000:ℝ)/(252056965953651/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1221 (x : ℝ) (h₁ : (1285/256:ℝ) ≤ x) (h₂ : x ≤ (2595/512:ℝ)) : (14162149/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/2000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (134223319/625000000:ℝ) := by nlinarith
  have hc1 : (7816225123/8000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (7816225123/8000000000:ℝ) ≤ taylorCos (134223319/625000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (998118115163/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/2000000000:ℝ) + taylorErr ≤ (998118115163/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (2452829361/40000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (2452829361/40000000000:ℝ) ≤ taylorSin (122718463/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (6659697571/31250000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (134223319/625000000:ℝ) + taylorErr ≤ (6659697571/31250000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-998118115163/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-7816225123/8000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-6659697571/31250000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-2452829361/40000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1971165312433/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15922720578253/1000000000000:ℝ) := by nlinarith
  have hp1 : (6524551591563/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13176040161261/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-5615900330071/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-800180585557/500000000000:ℝ) := by nlinarith
  have hN : (602243055951/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (126516515306561/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (602243055951/1000000000000:ℝ) (126516515306561/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (14162149/10000000000000:ℝ) ≤ ((602243055951/1000000000000:ℝ)/(126516515306561/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1222 (x : ℝ) (h₁ : (1285/256:ℝ) ≤ x) (h₂ : x ≤ (325/64:ℝ)) : (1405331/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/2000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2454369261/10000000000:ℝ) := by nlinarith
  have hc1 : (970031250923/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (970031250923/1000000000000:ℝ) ≤ taylorCos (2454369261/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (998118115163/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/2000000000:ℝ) + taylorErr ≤ (998118115163/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (2452829361/40000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (2452829361/40000000000:ℝ) ≤ taylorSin (122718463/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (242980182203/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2454369261/10000000000:ℝ) + taylorErr ≤ (242980182203/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-998118115163/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-970031250923/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-242980182203/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-2452829361/40000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1971165312433/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15953400194011/1000000000000:ℝ) := by nlinarith
  have hp1 : (6524551591563/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26402855043761/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-6415370529213/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-800180585557/500000000000:ℝ) := by nlinarith
  have hN : (602243055951/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (508021955500541/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (602243055951/1000000000000:ℝ) (508021955500541/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1405331/1000000000000:ℝ) ≤ ((602243055951/1000000000000:ℝ)/(508021955500541/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1223 (x : ℝ) (h₁ : (1285/256:ℝ) ≤ x) (h₂ : x ≤ (1305/256:ℝ)) : (13838751/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/2000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (383495197/1250000000:ℝ) := by nlinarith
  have hc1 : (190661207617/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (190661207617/200000000000:ℝ) ≤ taylorCos (383495197/1250000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (998118115163/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/2000000000:ℝ) + taylorErr ≤ (998118115163/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (2452829361/40000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (2452829361/40000000000:ℝ) ≤ taylorSin (122718463/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (302005951603/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (383495197/1250000000:ℝ) + taylorErr ≤ (302005951603/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-998118115163/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-190661207617/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-302005951603/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-2452829361/40000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1971165312433/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (16014759425527/1000000000000:ℝ) := by nlinarith
  have hp1 : (6524551591563/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13252202243119/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-4002243949269/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-800180585557/500000000000:ℝ) := by nlinarith
  have hN : (602243055951/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (127986259728753/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (602243055951/1000000000000:ℝ) (127986259728753/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (13838751/10000000000000:ℝ) ≤ ((602243055951/1000000000000:ℝ)/(127986259728753/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1224 (x : ℝ) (h₁ : (1285/256:ℝ) ≤ x) (h₂ : x ≤ (655/128:ℝ)) : (6814137/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/2000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (3681553891/10000000000:ℝ) := by nlinarith
  have hc1 : (93299279657/100000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (93299279657/100000000000:ℝ) ≤ taylorCos (3681553891/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (998118115163/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/2000000000:ℝ) + taylorErr ≤ (998118115163/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (2452829361/40000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (2452829361/40000000000:ℝ) ≤ taylorSin (122718463/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (89973759701/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3681553891/10000000000:ℝ) + taylorErr ≤ (89973759701/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-998118115163/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-93299279657/100000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-89973759701/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-2452829361/40000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1971165312433/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (8038059328521/500000000000:ℝ) := by nlinarith
  have hp1 : (6524551591563/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26605953928713/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1196918852699/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-800180585557/500000000000:ℝ) := by nlinarith
  have hN : (602243055951/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (128970795537647/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (602243055951/1000000000000:ℝ) (128970795537647/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (6814137/5000000000000:ℝ) ≤ ((602243055951/1000000000000:ℝ)/(128970795537647/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1225 (x : ℝ) (h₁ : (10281/2048:ℝ) ≤ x) (h₂ : x ≤ (647/128:ℝ)) : (8145961/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (628932123/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1718058483/10000000000:ℝ) := by nlinarith
  have hc1 : (985277640117/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (985277640117/1000000000000:ℝ) ≤ taylorCos (1718058483/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (499011438017/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (628932123/10000000000:ℝ) + taylorErr ≤ (499011438017/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (62851755299/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (62851755299/1000000000000:ℝ) ≤ taylorSin (628932123/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (85480945539/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1718058483/10000000000:ℝ) + taylorErr ≤ (85480945539/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-499011438017/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-985277640117/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-85480945539/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-62851755299/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3942714120063/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15879769116193/1000000000000:ℝ) := by nlinarith
  have hp1 : (652518627557/25000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2628099571279/100000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-561631090809/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-164047764429/100000000000:ℝ) := by nlinarith
  have hN : (5019177877/7812500000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (100666826873439/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (5019177877/7812500000:ℝ) (100666826873439/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (8145961/5000000000000:ℝ) ≤ ((5019177877/7812500000:ℝ)/(100666826873439/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1226 (x : ℝ) (h₁ : (643/128:ℝ) ≤ x) (h₂ : x ≤ (10399/2048:ℝ)) : (33101423/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (368155389/5000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2439029453/10000000000:ℝ) := by nlinarith
  have hc1 : (970402836419/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (970402836419/1000000000000:ℝ) ≤ taylorCos (2439029453/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (498645229471/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (368155389/5000000000:ℝ) + taylorErr ≤ (498645229471/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (73564561319/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (73564561319/1000000000000:ℝ) ≤ taylorSin (368155389/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (24149188759/100000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2439029453/10000000000:ℝ) + taylorErr ≤ (24149188759/100000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-498645229471/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-970402836419/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-24149188759/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-73564561319/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15781594345767/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15951866213223/1000000000000:ℝ) := by nlinarith
  have hp1 : (13059258127237/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26400316307699/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-159386555453/25000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1921397190563/1000000000000:ℝ) := by nlinarith
  have hN : (924106731621/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (507924071369131/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (924106731621/1000000000000:ℝ) (507924071369131/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (33101423/10000000000000:ℝ) ≤ ((924106731621/1000000000000:ℝ)/(507924071369131/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1227 (x : ℝ) (h₁ : (643/128:ℝ) ≤ x) (h₂ : x ≤ (5235/1024:ℝ)) : (32210921/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (368155389/5000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (3528155813/10000000000:ℝ) := by nlinarith
  have hc1 : (938403531771/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (938403531771/1000000000000:ℝ) ≤ taylorCos (3528155813/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (498645229471/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (368155389/5000000000:ℝ) + taylorErr ≤ (498645229471/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (73564561319/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (73564561319/1000000000000:ℝ) ≤ taylorSin (368155389/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (345541327307/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3528155813/10000000000:ℝ) + taylorErr ≤ (345541327307/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-498645229471/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-938403531771/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-345541327307/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-73564561319/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15781594345767/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (16060778849163/1000000000000:ℝ) := by nlinarith
  have hp1 : (13059258127237/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13290283284047/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-287021382891/31250000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1921397190563/1000000000000:ℝ) := by nlinarith
  have hN : (924106731621/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (128724308620861/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (924106731621/1000000000000:ℝ) (128724308620861/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (32210921/10000000000000:ℝ) ≤ ((924106731621/1000000000000:ℝ)/(128724308620861/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1228 (x : ℝ) (h₁ : (5145/1024:ℝ) ≤ x) (h₂ : x ≤ (5165/1024:ℝ)) : (10044841/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (766990393/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (138058271/1000000000:ℝ) := by nlinarith
  have hc1 : (495242540991/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (495242540991/500000000000:ℝ) ≤ taylorCos (138058271/1000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (997060072609/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (766990393/10000000000:ℝ) + taylorErr ≤ (997060072609/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (19155964759/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (19155964759/250000000000:ℝ) ≤ taylorSin (766990393/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (68810061969/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (138058271/1000000000:ℝ) + taylorErr ≤ (68810061969/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-997060072609/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-495242540991/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-68810061969/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-19155964759/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15784662307343/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15846021538859/1000000000000:ℝ) := by nlinarith
  have hp1 : (2612359372653/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (6556285879857/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-902276875359/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-400338112643/200000000000:ℝ) := by nlinarith
  have hN : (502315245303/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (501192797219967/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (502315245303/500000000000:ℝ) (501192797219967/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (10044841/2500000000000:ℝ) ≤ ((502315245303/500000000000:ℝ)/(501192797219967/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1229 (x : ℝ) (h₁ : (5145/1024:ℝ) ≤ x) (h₂ : x ≤ (2585/512:ℝ)) : (5002981/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (766990393/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (383495197/2500000000:ℝ) := by nlinarith
  have hc1 : (988257565467/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (988257565467/1000000000000:ℝ) ≤ taylorCos (383495197/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (997060072609/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (766990393/10000000000:ℝ) + taylorErr ≤ (997060072609/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (19155964759/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (19155964759/250000000000:ℝ) ≤ taylorSin (766990393/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (38199296883/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (383495197/2500000000:ℝ) + taylorErr ≤ (38199296883/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-997060072609/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-988257565467/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-38199296883/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-19155964759/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15784662307343/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (7930680673369/500000000000:ℝ) := by nlinarith
  have hp1 : (2612359372653/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26250530880047/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2005503644847/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-400338112643/200000000000:ℝ) := by nlinarith
  have hN : (502315245303/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (502165567543589/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (502315245303/500000000000:ℝ) (502165567543589/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (5002981/1250000000000:ℝ) ≤ ((502315245303/500000000000:ℝ)/(502165567543589/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1230 (x : ℝ) (h₁ : (5145/1024:ℝ) ≤ x) (h₂ : x ≤ (20691/4096:ℝ)) : (7987727/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (766990393/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (404587433/2500000000:ℝ) := by nlinarith
  have hc1 : (986933274579/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (986933274579/1000000000000:ℝ) ≤ taylorCos (404587433/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (997060072609/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (766990393/10000000000:ℝ) + taylorErr ≤ (997060072609/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (19155964759/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (19155964759/250000000000:ℝ) ≤ taylorSin (766990393/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (32225895049/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (404587433/2500000000:ℝ) + taylorErr ≤ (32225895049/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-997060072609/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-986933274579/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-32225895049/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-19155964759/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15784662307343/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15869798241071/1000000000000:ℝ) := by nlinarith
  have hp1 : (2612359372653/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26264493928387/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-4231984124257/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-400338112643/200000000000:ℝ) := by nlinarith
  have hN : (502315245303/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (502700992424601/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (502315245303/500000000000:ℝ) (502700992424601/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (7987727/2000000000000:ℝ) ≤ ((502315245303/500000000000:ℝ)/(502700992424601/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1231 (x : ℝ) (h₁ : (5145/1024:ℝ) ≤ x) (h₂ : x ≤ (10361/2048:ℝ)) : (39699707/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (766990393/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (928058377/5000000000:ℝ) := by nlinarith
  have hc1 : (245705887231/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (245705887231/250000000000:ℝ) ≤ taylorCos (928058377/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (997060072609/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (766990393/10000000000:ℝ) + taylorErr ≤ (997060072609/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (19155964759/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (19155964759/250000000000:ℝ) ≤ taylorSin (766990393/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (36909547853/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (928058377/5000000000:ℝ) + taylorErr ≤ (36909547853/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-997060072609/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-245705887231/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-36909547853/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-19155964759/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15784662307343/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3973393735821/250000000000:ℝ) := by nlinarith
  have hp1 : (2612359372653/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26303844337347/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1213578751609/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-400338112643/200000000000:ℝ) := by nlinarith
  have hN : (502315245303/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (504211448955571/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (502315245303/500000000000:ℝ) (504211448955571/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (39699707/10000000000000:ℝ) ≤ ((502315245303/500000000000:ℝ)/(504211448955571/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1232 (x : ℝ) (h₁ : (2573/512:ℝ) ≤ x) (h₂ : x ≤ (10383/2048:ℝ)) : (45928559/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (797670009/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2193592527/10000000000:ℝ) := by nlinarith
  have hc1 : (97603707677/100000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (97603707677/100000000000:ℝ) ≤ taylorCos (2193592527/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (996820301559/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (797670009/10000000000:ℝ) + taylorErr ≤ (996820301559/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (79682435639/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (79682435639/1000000000000:ℝ) ≤ taylorSin (797670009/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (54401069233/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2193592527/10000000000:ℝ) + taylorErr ≤ (54401069233/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-996820301559/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-97603707677/100000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-54401069233/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-79682435639/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15787730268919/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15927322520617/1000000000000:ℝ) := by nlinarith
  have hp1 : (13064335599293/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (6589924132677/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-179249459491/31250000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2081996161113/1000000000000:ℝ) := by nlinarith
  have hN : (542587929777/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (506359205351507/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (542587929777/500000000000:ℝ) (506359205351507/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (45928559/10000000000000:ℝ) ≤ ((542587929777/500000000000:ℝ)/(506359205351507/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1233 (x : ℝ) (h₁ : (2573/512:ℝ) ≤ x) (h₂ : x ≤ (661/128:ℝ)) : (42660549/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (797670009/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (644271931/1250000000:ℝ) := by nlinarith
  have hc1 : (870086988811/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (870086988811/1000000000000:ℝ) ≤ taylorCos (644271931/1250000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (996820301559/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (797670009/10000000000:ℝ) + taylorErr ≤ (996820301559/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (79682435639/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (79682435639/1000000000000:ℝ) ≤ taylorSin (797670009/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (492898194553/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (644271931/1250000000:ℝ) + taylorErr ≤ (492898194553/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-996820301559/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-870086988811/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-492898194553/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-79682435639/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15787730268919/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (16223380812679/1000000000000:ℝ) := by nlinarith
  have hp1 : (13064335599293/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5369934518131/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-6617077572137/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2081996161113/1000000000000:ℝ) := by nlinarith
  have hN : (542587929777/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (525396169986403/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (542587929777/500000000000:ℝ) (525396169986403/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (42660549/10000000000000:ℝ) ≤ ((542587929777/500000000000:ℝ)/(525396169986403/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1234 (x : ℝ) (h₁ : (2573/512:ℝ) ≤ x) (h₂ : x ≤ (333/64:ℝ)) : (41391449/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (797670009/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (3190680039/5000000000:ℝ) := by nlinarith
  have hc1 : (160641505837/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (160641505837/200000000000:ℝ) ≤ taylorCos (3190680039/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (996820301559/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (797670009/10000000000:ℝ) + taylorErr ≤ (996820301559/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (79682435639/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (79682435639/1000000000000:ℝ) ≤ taylorSin (797670009/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (297849653393/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3190680039/5000000000:ℝ) + taylorErr ≤ (297849653393/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-996820301559/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-160641505837/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-297849653393/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-79682435639/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15787730268919/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1634609927571/100000000000:ℝ) := by nlinarith
  have hp1 : (13064335599293/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3381596434451/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-805765860733/50000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2081996161113/1000000000000:ℝ) := by nlinarith
  have hN : (542587929777/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (266694961531367/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (542587929777/500000000000:ℝ) (266694961531367/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (41391449/10000000000000:ℝ) ≤ ((542587929777/500000000000:ℝ)/(266694961531367/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1235 (x : ℝ) (h₁ : (20589/4096:ℝ) ≤ x) (h₂ : x ≤ (5175/1024:ℝ)) : (55553319/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (836019529/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1687378867/10000000000:ℝ) := by nlinarith
  have hc1 : (9857975069/10000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (9857975069/10000000000:ℝ) ≤ taylorCos (1687378867/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (498253696973/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (836019529/10000000000:ℝ) + taylorErr ≤ (498253696973/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (83504598331/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (83504598331/1000000000000:ℝ) ≤ taylorSin (836019529/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (167938297269/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1687378867/10000000000:ℝ) + taylorErr ≤ (167938297269/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-498253696973/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-9857975069/10000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-167938297269/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-83504598331/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1973945652611/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15876701154617/1000000000000:ℝ) := by nlinarith
  have hp1 : (5227003607731/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13137959120333/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-4412732968517/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2182394183691/1000000000000:ℝ) := by nlinarith
  have hN : (237177357949/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (251569639553017/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (237177357949/200000000000:ℝ) (251569639553017/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (55553319/10000000000000:ℝ) ≤ ((237177357949/200000000000:ℝ)/(251569639553017/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1236 (x : ℝ) (h₁ : (10299/2048:ℝ) ≤ x) (h₂ : x ≤ (20709/4096:ℝ)) : (73715499/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (113131083/1250000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1756408003/10000000000:ℝ) := by nlinarith
  have hc1 : (984614765927/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (984614765927/1000000000000:ℝ) ≤ taylorCos (1756408003/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (995907231687/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (113131083/1250000000:ℝ) + taylorErr ≤ (995907231687/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (90381358531/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (90381358531/1000000000000:ℝ) ≤ taylorSin (113131083/1250000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (21842389641/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1756408003/10000000000:ℝ) + taylorErr ≤ (21842389641/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-995907231687/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-984614765927/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-21842389641/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-90381358531/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7899234067217/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (7941802034081/500000000000:ℝ) := by nlinarith
  have hp1 : (26146442350781/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1642958909559/62500000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-4593427029343/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-36924234069/15625000000:ℝ) := by nlinarith
  have hN : (1367243748729/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (100715551277653/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1367243748729/1000000000000:ℝ) (100715551277653/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (73715499/10000000000000:ℝ) ≤ ((1367243748729/1000000000000:ℝ)/(100715551277653/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1237 (x : ℝ) (h₁ : (2575/512:ℝ) ≤ x) (h₂ : x ≤ (5165/1024:ℝ)) : (19718007/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (115048559/1250000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (138058271/1000000000:ℝ) := by nlinarith
  have hc1 : (495242540991/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (495242540991/500000000000:ℝ) ≤ taylorCos (138058271/1000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (995767416737/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (115048559/1250000000:ℝ) + taylorErr ≤ (995767416737/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (45954477081/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (45954477081/500000000000:ℝ) ≤ taylorSin (115048559/1250000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (68810061969/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (138058271/1000000000:ℝ) + taylorErr ≤ (68810061969/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-995767416737/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-495242540991/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-68810061969/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-45954477081/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7900001057611/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15846021538859/1000000000000:ℝ) := by nlinarith
  have hp1 : (26148981086809/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (6556285879857/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-902276875359/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-240332550409/100000000000:ℝ) := by nlinarith
  have hN : (1407558087353/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (501192797219967/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1407558087353/1000000000000:ℝ) (501192797219967/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (19718007/2500000000000:ℝ) ≤ ((1407558087353/1000000000000:ℝ)/(501192797219967/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1238 (x : ℝ) (h₁ : (2575/512:ℝ) ≤ x) (h₂ : x ≤ (2585/512:ℝ)) : (314267/40000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (115048559/1250000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (383495197/2500000000:ℝ) := by nlinarith
  have hc1 : (988257565467/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (988257565467/1000000000000:ℝ) ≤ taylorCos (383495197/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (995767416737/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (115048559/1250000000:ℝ) + taylorErr ≤ (995767416737/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (45954477081/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (45954477081/500000000000:ℝ) ≤ taylorSin (115048559/1250000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (38199296883/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (383495197/2500000000:ℝ) + taylorErr ≤ (38199296883/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-995767416737/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-988257565467/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-38199296883/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-45954477081/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7900001057611/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (7930680673369/500000000000:ℝ) := by nlinarith
  have hp1 : (26148981086809/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26250530880047/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2005503644847/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-240332550409/100000000000:ℝ) := by nlinarith
  have hN : (1407558087353/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (502165567543589/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1407558087353/1000000000000:ℝ) (502165567543589/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (314267/40000000000:ℝ) ≤ ((1407558087353/1000000000000:ℝ)/(502165567543589/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1239 (x : ℝ) (h₁ : (2575/512:ℝ) ≤ x) (h₂ : x ≤ (5175/1024:ℝ)) : (19565737/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (115048559/1250000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1687378867/10000000000:ℝ) := by nlinarith
  have hc1 : (9857975069/10000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (9857975069/10000000000:ℝ) ≤ taylorCos (1687378867/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (995767416737/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (115048559/1250000000:ℝ) + taylorErr ≤ (995767416737/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (45954477081/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (45954477081/500000000000:ℝ) ≤ taylorSin (115048559/1250000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (167938297269/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1687378867/10000000000:ℝ) + taylorErr ≤ (167938297269/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-995767416737/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-9857975069/10000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-167938297269/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-45954477081/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7900001057611/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15876701154617/1000000000000:ℝ) := by nlinarith
  have hp1 : (26148981086809/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13137959120333/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-4412732968517/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-240332550409/100000000000:ℝ) := by nlinarith
  have hN : (1407558087353/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (251569639553017/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1407558087353/1000000000000:ℝ) (251569639553017/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (19565737/2500000000000:ℝ) ≤ ((1407558087353/1000000000000:ℝ)/(251569639553017/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1240 (x : ℝ) (h₁ : (2575/512:ℝ) ≤ x) (h₂ : x ≤ (1295/256:ℝ)) : (38980307/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (115048559/1250000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (920388473/5000000000:ℝ) := by nlinarith
  have hc1 : (983105485159/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (983105485159/1000000000000:ℝ) ≤ taylorCos (920388473/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (995767416737/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (115048559/1250000000:ℝ) + taylorErr ≤ (995767416737/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (45954477081/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (45954477081/500000000000:ℝ) ≤ taylorSin (115048559/1250000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (18303989027/100000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (920388473/5000000000:ℝ) + taylorErr ≤ (18303989027/100000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-995767416737/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-983105485159/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-18303989027/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-45954477081/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7900001057611/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (248313140039/15625000000:ℝ) := by nlinarith
  have hp1 : (26148981086809/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5260261120257/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-4814188091217/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-240332550409/100000000000:ℝ) := by nlinarith
  have hN : (1407558087353/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (252056965953651/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1407558087353/1000000000000:ℝ) (252056965953651/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (38980307/5000000000000:ℝ) ≤ ((1407558087353/1000000000000:ℝ)/(252056965953651/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1241 (x : ℝ) (h₁ : (2575/512:ℝ) ≤ x) (h₂ : x ≤ (2595/512:ℝ)) : (38680157/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (115048559/1250000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (134223319/625000000:ℝ) := by nlinarith
  have hc1 : (7816225123/8000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (7816225123/8000000000:ℝ) ≤ taylorCos (134223319/625000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (995767416737/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (115048559/1250000000:ℝ) + taylorErr ≤ (995767416737/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (45954477081/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (45954477081/500000000000:ℝ) ≤ taylorSin (115048559/1250000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (6659697571/31250000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (134223319/625000000:ℝ) + taylorErr ≤ (6659697571/31250000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-995767416737/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-7816225123/8000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-6659697571/31250000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-45954477081/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7900001057611/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15922720578253/1000000000000:ℝ) := by nlinarith
  have hp1 : (26148981086809/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13176040161261/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-5615900330071/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-240332550409/100000000000:ℝ) := by nlinarith
  have hN : (1407558087353/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (126516515306561/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1407558087353/1000000000000:ℝ) (126516515306561/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (38680157/5000000000000:ℝ) ≤ ((1407558087353/1000000000000:ℝ)/(126516515306561/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1242 (x : ℝ) (h₁ : (2575/512:ℝ) ≤ x) (h₂ : x ≤ (325/64:ℝ)) : (76765783/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (115048559/1250000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2454369261/10000000000:ℝ) := by nlinarith
  have hc1 : (970031250923/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (970031250923/1000000000000:ℝ) ≤ taylorCos (2454369261/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (995767416737/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (115048559/1250000000:ℝ) + taylorErr ≤ (995767416737/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (45954477081/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (45954477081/500000000000:ℝ) ≤ taylorSin (115048559/1250000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (242980182203/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2454369261/10000000000:ℝ) + taylorErr ≤ (242980182203/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-995767416737/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-970031250923/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-242980182203/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-45954477081/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7900001057611/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15953400194011/1000000000000:ℝ) := by nlinarith
  have hp1 : (26148981086809/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26402855043761/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-6415370529213/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-240332550409/100000000000:ℝ) := by nlinarith
  have hN : (1407558087353/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (508021955500541/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1407558087353/1000000000000:ℝ) (508021955500541/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (76765783/10000000000000:ℝ) ≤ ((1407558087353/1000000000000:ℝ)/(508021955500541/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1243 (x : ℝ) (h₁ : (10301/2048:ℝ) ≤ x) (h₂ : x ≤ (2593/512:ℝ)) : (82109019/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (23393207/250000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2024854641/10000000000:ℝ) := by nlinarith
  have hc1 : (979569763403/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (979569763403/1000000000000:ℝ) ≤ taylorCos (2024854641/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (995625258649/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (23393207/250000000:ℝ) + taylorErr ≤ (995625258649/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (93436333523/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (93436333523/1000000000000:ℝ) ≤ taylorSin (23393207/250000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (201104637201/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2024854641/10000000000:ℝ) + taylorErr ≤ (201104637201/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-995625258649/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-979569763403/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-201104637201/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-93436333523/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15801536096009/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (318208974639/20000000000:ℝ) := by nlinarith
  have hp1 : (5230303964567/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26331770434027/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1323860284999/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2443502128299/1000000000000:ℝ) := by nlinarith
  have hN : (28957537393/20000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (505284757704019/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (28957537393/20000000000:ℝ) (505284757704019/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (82109019/10000000000000:ℝ) ≤ ((28957537393/20000000000:ℝ)/(505284757704019/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1244 (x : ℝ) (h₁ : (10301/2048:ℝ) ≤ x) (h₂ : x ≤ (1299/256:ℝ)) : (81477507/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (23393207/250000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1165825399/5000000000:ℝ) := by nlinarith
  have hc1 : (486469974967/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (486469974967/500000000000:ℝ) ≤ taylorCos (1165825399/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (995625258649/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (23393207/250000000:ℝ) + taylorErr ≤ (995625258649/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (93436333523/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (93436333523/1000000000000:ℝ) ≤ taylorSin (23393207/250000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (231058110583/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1165825399/5000000000:ℝ) + taylorErr ≤ (231058110583/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-995625258649/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-486469974967/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-231058110583/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-93436333523/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15801536096009/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3985282086927/250000000000:ℝ) := by nlinarith
  have hp1 : (5230303964567/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13191272577633/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-6095901035947/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2443502128299/1000000000000:ℝ) := by nlinarith
  have hN : (28957537393/20000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (2536195729981/5000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (28957537393/20000000000:ℝ) (2536195729981/5000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (81477507/10000000000000:ℝ) ≤ ((28957537393/20000000000:ℝ)/(2536195729981/5000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1245 (x : ℝ) (h₁ : (20611/4096:ℝ) ≤ x) (h₂ : x ≤ (10351/2048:ℝ)) : (104831431/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (125594677/1250000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (68108747/400000000:ℝ) := by nlinarith
  have hc1 : (492769366521/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (492769366521/500000000000:ℝ) ≤ taylorCos (68108747/400000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (994956560033/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (125594677/1250000000:ℝ) + taylorErr ≤ (994956560033/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (100306767943/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (100306767943/1000000000000:ℝ) ≤ taylorSin (125594677/1250000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (8472514677/50000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (68108747/400000000:ℝ) + taylorErr ≤ (8472514677/50000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-994956560033/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-492769366521/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-8472514677/50000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-100306767943/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3161687801911/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3175647027081/200000000000:ℝ) := by nlinarith
  have hp1 : (26162944134961/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3284807122091/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-890578449697/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2624320366051/1000000000000:ℝ) := by nlinarith
  have hN : (814681903009/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (25161835101521/50000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (814681903009/500000000000:ℝ) (25161835101521/50000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (104831431/10000000000000:ℝ) ≤ ((814681903009/500000000000:ℝ)/(25161835101521/50000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1246 (x : ℝ) (h₁ : (5155/1024:ℝ) ≤ x) (h₂ : x ≤ (10335/2048:ℝ)) : (13030209/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1073786551/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1457281749/10000000000:ℝ) := by nlinarith
  have hc1 : (494700212761/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (494700212761/500000000000:ℝ) ≤ taylorCos (1457281749/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (994240451721/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1073786551/10000000000:ℝ) + taylorErr ≤ (994240451721/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (107172422643/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (107172422643/1000000000000:ℝ) ≤ taylorSin (1073786551/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (29042585393/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1457281749/10000000000:ℝ) + taylorErr ≤ (29042585393/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-994240451721/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-494700212761/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-29042585393/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-107172422643/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (158153419231/10000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15853691442799/1000000000000:ℝ) := by nlinarith
  have hp1 : (13087184223543/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13118918599869/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1905036568503/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-350646309703/125000000000:ℝ) := by nlinarith
  have hN : (1810930025903/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (501679064726957/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1810930025903/1000000000000:ℝ) (501679064726957/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (13030209/1000000000000:ℝ) ≤ ((1810930025903/1000000000000:ℝ)/(501679064726957/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1247 (x : ℝ) (h₁ : (5155/1024:ℝ) ≤ x) (h₂ : x ≤ (2585/512:ℝ)) : (16256217/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1073786551/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (383495197/2500000000:ℝ) := by nlinarith
  have hc1 : (988257565467/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (988257565467/1000000000000:ℝ) ≤ taylorCos (383495197/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (994240451721/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1073786551/10000000000:ℝ) + taylorErr ≤ (994240451721/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (107172422643/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (107172422643/1000000000000:ℝ) ≤ taylorSin (1073786551/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (38199296883/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (383495197/2500000000:ℝ) + taylorErr ≤ (38199296883/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-994240451721/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-988257565467/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-38199296883/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-107172422643/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (158153419231/10000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (7930680673369/500000000000:ℝ) := by nlinarith
  have hp1 : (13087184223543/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26250530880047/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2005503644847/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-350646309703/125000000000:ℝ) := by nlinarith
  have hN : (1810930025903/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (502165567543589/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1810930025903/1000000000000:ℝ) (502165567543589/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (16256217/1250000000000:ℝ) ≤ ((1810930025903/1000000000000:ℝ)/(502165567543589/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1248 (x : ℝ) (h₁ : (5155/1024:ℝ) ≤ x) (h₂ : x ≤ (20691/4096:ℝ)) : (129772853/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1073786551/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (404587433/2500000000:ℝ) := by nlinarith
  have hc1 : (986933274579/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (986933274579/1000000000000:ℝ) ≤ taylorCos (404587433/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (994240451721/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1073786551/10000000000:ℝ) + taylorErr ≤ (994240451721/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (107172422643/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (107172422643/1000000000000:ℝ) ≤ taylorSin (1073786551/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (32225895049/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (404587433/2500000000:ℝ) + taylorErr ≤ (32225895049/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-994240451721/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-986933274579/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-32225895049/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-107172422643/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (158153419231/10000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15869798241071/1000000000000:ℝ) := by nlinarith
  have hp1 : (13087184223543/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26264493928387/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-4231984124257/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-350646309703/125000000000:ℝ) := by nlinarith
  have hN : (1810930025903/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (502700992424601/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1810930025903/1000000000000:ℝ) (502700992424601/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (129772853/10000000000000:ℝ) ≤ ((1810930025903/1000000000000:ℝ)/(502700992424601/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1249 (x : ℝ) (h₁ : (5155/1024:ℝ) ≤ x) (h₂ : x ≤ (5175/1024:ℝ)) : (6477343/500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1073786551/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1687378867/10000000000:ℝ) := by nlinarith
  have hc1 : (9857975069/10000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (9857975069/10000000000:ℝ) ≤ taylorCos (1687378867/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (994240451721/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1073786551/10000000000:ℝ) + taylorErr ≤ (994240451721/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (107172422643/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (107172422643/1000000000000:ℝ) ≤ taylorSin (1073786551/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (167938297269/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1687378867/10000000000:ℝ) + taylorErr ≤ (167938297269/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-994240451721/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-9857975069/10000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-167938297269/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-107172422643/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (158153419231/10000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15876701154617/1000000000000:ℝ) := by nlinarith
  have hp1 : (13087184223543/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13137959120333/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-4412732968517/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-350646309703/125000000000:ℝ) := by nlinarith
  have hN : (1810930025903/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (251569639553017/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1810930025903/1000000000000:ℝ) (251569639553017/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (6477343/500000000000:ℝ) ≤ ((1810930025903/1000000000000:ℝ)/(251569639553017/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1250 (x : ℝ) (h₁ : (5155/1024:ℝ) ≤ x) (h₂ : x ≤ (1295/256:ℝ)) : (129046413/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1073786551/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (920388473/5000000000:ℝ) := by nlinarith
  have hc1 : (983105485159/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (983105485159/1000000000000:ℝ) ≤ taylorCos (920388473/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (994240451721/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1073786551/10000000000:ℝ) + taylorErr ≤ (994240451721/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (107172422643/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (107172422643/1000000000000:ℝ) ≤ taylorSin (1073786551/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (18303989027/100000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (920388473/5000000000:ℝ) + taylorErr ≤ (18303989027/100000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-994240451721/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-983105485159/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-18303989027/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-107172422643/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (158153419231/10000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (248313140039/15625000000:ℝ) := by nlinarith
  have hp1 : (13087184223543/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5260261120257/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-4814188091217/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-350646309703/125000000000:ℝ) := by nlinarith
  have hN : (1810930025903/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (252056965953651/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1810930025903/1000000000000:ℝ) (252056965953651/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (129046413/10000000000000:ℝ) ≤ ((1810930025903/1000000000000:ℝ)/(252056965953651/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1251 (x : ℝ) (h₁ : (5155/1024:ℝ) ≤ x) (h₂ : x ≤ (20731/4096:ℝ)) : (64386099/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1073786551/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1925145889/10000000000:ℝ) := by nlinarith
  have hc1 : (981526226193/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (981526226193/1000000000000:ℝ) ≤ taylorCos (1925145889/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (994240451721/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1073786551/10000000000:ℝ) + taylorErr ≤ (994240451721/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (107172422643/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (107172422643/1000000000000:ℝ) ≤ taylorSin (1073786551/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (95663817247/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1925145889/10000000000:ℝ) + taylorErr ≤ (95663817247/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-994240451721/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-981526226193/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-95663817247/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-107172422643/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (158153419231/10000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15900477856829/1000000000000:ℝ) := by nlinarith
  have hp1 : (13087184223543/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (210522149197/8000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-5034838101807/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-350646309703/125000000000:ℝ) := by nlinarith
  have hN : (1810930025903/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (504650392151019/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1810930025903/1000000000000:ℝ) (504650392151019/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (64386099/5000000000000:ℝ) ≤ ((1810930025903/1000000000000:ℝ)/(504650392151019/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1252 (x : ℝ) (h₁ : (5155/1024:ℝ) ≤ x) (h₂ : x ≤ (10421/2048:ℝ)) : (31511369/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1073786551/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2776505227/10000000000:ℝ) := by nlinarith
  have hc1 : (480851037121/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (480851037121/500000000000:ℝ) ≤ taylorCos (2776505227/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (994240451721/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1073786551/10000000000:ℝ) + taylorErr ≤ (994240451721/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (107172422643/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (107172422643/1000000000000:ℝ) ≤ taylorSin (1073786551/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (13704845611/50000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2776505227/10000000000:ℝ) + taylorErr ≤ (13704845611/50000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-994240451721/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-480851037121/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-13704845611/50000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-107172422643/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (158153419231/10000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15985613790557/1000000000000:ℝ) := by nlinarith
  have hp1 : (13087184223543/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26456168501061/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-7251554095313/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-350646309703/125000000000:ℝ) := by nlinarith
  have hN : (1810930025903/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (510079696521693/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1810930025903/1000000000000:ℝ) (510079696521693/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (31511369/2500000000000:ℝ) ≤ ((1810930025903/1000000000000:ℝ)/(510079696521693/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1253 (x : ℝ) (h₁ : (5155/1024:ℝ) ≤ x) (h₂ : x ≤ (2613/512:ℝ)) : (2491077/200000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1073786551/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (3252039271/10000000000:ℝ) := by nlinarith
  have hc1 : (473792794367/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (473792794367/500000000000:ℝ) ≤ taylorCos (3252039271/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (994240451721/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1073786551/10000000000:ℝ) + taylorErr ≤ (994240451721/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (107172422643/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (107172422643/1000000000000:ℝ) ≤ taylorSin (1073786551/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (319502033143/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3252039271/10000000000:ℝ) + taylorErr ≤ (319502033143/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-994240451721/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-473792794367/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-319502033143/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-107172422643/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (158153419231/10000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (16033167194981/1000000000000:ℝ) := by nlinarith
  have hp1 : (13087184223543/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26534869318979/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-4238972348299/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-350646309703/125000000000:ℝ) := by nlinarith
  have hN : (1810930025903/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (51312490060443/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1810930025903/1000000000000:ℝ) (51312490060443/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2491077/200000000000:ℝ) ≤ ((1810930025903/1000000000000:ℝ)/(51312490060443/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1254 (x : ℝ) (h₁ : (1289/256:ℝ) ≤ x) (h₂ : x ≤ (10383/2048:ℝ)) : (139560919/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1104466167/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2193592527/10000000000:ℝ) := by nlinarith
  have hc1 : (97603707677/100000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (97603707677/100000000000:ℝ) ≤ taylorCos (2193592527/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (248476743067/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1104466167/10000000000:ℝ) + taylorErr ≤ (248476743067/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (27555551251/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (27555551251/250000000000:ℝ) ≤ taylorSin (1104466167/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (54401069233/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2193592527/10000000000:ℝ) + taylorErr ≤ (54401069233/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-248476743067/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-97603707677/100000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-54401069233/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-27555551251/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3954602471169/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15927322520617/1000000000000:ℝ) := by nlinarith
  have hp1 : (13089722959571/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (6589924132677/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-179249459491/31250000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-288555625499/100000000000:ℝ) := by nlinarith
  have hN : (945824641361/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (506359205351507/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (945824641361/500000000000:ℝ) (506359205351507/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (139560919/10000000000000:ℝ) ≤ ((945824641361/500000000000:ℝ)/(506359205351507/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1255 (x : ℝ) (h₁ : (1289/256:ℝ) ≤ x) (h₂ : x ≤ (10403/2048:ℝ)) : (4327771/312500000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1104466167/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (500077737/2000000000:ℝ) := by nlinarith
  have hc1 : (15139106289/15625000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (15139106289/15625000000:ℝ) ≤ taylorCos (500077737/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (248476743067/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1104466167/10000000000:ℝ) + taylorErr ≤ (248476743067/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (27555551251/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (27555551251/250000000000:ℝ) ≤ taylorSin (1104466167/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (123720810751/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (500077737/2000000000:ℝ) + taylorErr ≤ (123720810751/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-248476743067/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-15139106289/15625000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-123720810751/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-27555551251/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3954602471169/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (127664017091/8000000000:ℝ) := by nlinarith
  have hp1 : (13089722959571/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26410471251947/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-3267524915607/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-288555625499/100000000000:ℝ) := by nlinarith
  have hN : (945824641361/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (508315664369099/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (945824641361/500000000000:ℝ) (508315664369099/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (4327771/312500000000:ℝ) ≤ ((945824641361/500000000000:ℝ)/(508315664369099/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1256 (x : ℝ) (h₁ : (20629/4096:ℝ) ≤ x) (h₂ : x ≤ (5185/1024:ℝ)) : (155628467/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (571407843/5000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (79767001/400000000:ℝ) := by nlinarith
  have hc1 : (980182133691/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (980182133691/1000000000000:ℝ) ≤ taylorCos (79767001/400000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (496738483913/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (571407843/5000000000:ℝ) + taylorErr ≤ (496738483913/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (57016485287/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (57016485287/500000000000:ℝ) ≤ taylorSin (571407843/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (198098413053/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (79767001/400000000:ℝ) + taylorErr ≤ (198098413053/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-496738483913/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-980182133691/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-198098413053/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-57016485287/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7911122418323/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (127259046163/8000000000:ℝ) := by nlinarith
  have hp1 : (6546448189803/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5265338592381/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-5215276096687/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-23328466681/7812500000:ℝ) := by nlinarith
  have hN : (996283383671/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (505089525947393/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (996283383671/500000000000:ℝ) (505089525947393/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (155628467/10000000000000:ℝ) ≤ ((996283383671/500000000000:ℝ)/(505089525947393/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1257 (x : ℝ) (h₁ : (10315/2048:ℝ) ≤ x) (h₂ : x ≤ (2585/512:ℝ)) : (160652293/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (115048559/1000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (383495197/2500000000:ℝ) := by nlinarith
  have hc1 : (988257565467/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (988257565467/1000000000000:ℝ) ≤ taylorCos (383495197/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (993389213421/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (115048559/1000000000:ℝ) + taylorErr ≤ (993389213421/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (57397462127/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (57397462127/500000000000:ℝ) ≤ taylorSin (115048559/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (38199296883/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (383495197/2500000000:ℝ) + taylorErr ≤ (38199296883/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-993389213421/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-988257565467/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-38199296883/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-57397462127/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (98893823919/6250000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (7930680673369/500000000000:ℝ) := by nlinarith
  have hp1 : (13093531063613/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26250530880047/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2005503644847/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-3006141813329/1000000000000:ℝ) := by nlinarith
  have hN : (503188149977/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (502165567543589/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (503188149977/250000000000:ℝ) (502165567543589/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (160652293/10000000000000:ℝ) ≤ ((503188149977/250000000000:ℝ)/(502165567543589/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1258 (x : ℝ) (h₁ : (20631/4096:ℝ) ≤ x) (h₂ : x ≤ (10361/2048:ℝ)) : (81281811/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (579077747/5000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (928058377/5000000000:ℝ) := by nlinarith
  have hc1 : (245705887231/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (245705887231/250000000000:ℝ) ≤ taylorCos (928058377/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (99330087463/100000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (579077747/5000000000:ℝ) + taylorErr ≤ (99330087463/100000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (57778405201/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (57778405201/500000000000:ℝ) ≤ taylorSin (579077747/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (36909547853/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (928058377/5000000000:ℝ) + taylorErr ≤ (36909547853/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-99330087463/100000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-245705887231/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-36909547853/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-57778405201/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7911889408717/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3973393735821/250000000000:ℝ) := by nlinarith
  have hp1 : (654708287381/25000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26303844337347/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1213578751609/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-151312002867/50000000000:ℝ) := by nlinarith
  have hN : (203293918271/100000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (504211448955571/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (203293918271/100000000000:ℝ) (504211448955571/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (81281811/5000000000000:ℝ) ≤ ((203293918271/100000000000:ℝ)/(504211448955571/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1259 (x : ℝ) (h₁ : (10319/2048:ℝ) ≤ x) (h₂ : x ≤ (20749/4096:ℝ)) : (46245893/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (605922411/5000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (6447513/31250000:ℝ) := by nlinarith
  have hc1 : (195758267101/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (195758267101/200000000000:ℝ) ≤ taylorCos (6447513/31250000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (248166536179/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (605922411/5000000000:ℝ) + taylorErr ≤ (248166536179/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (120888084931/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (120888084931/1000000000000:ℝ) ≤ taylorSin (605922411/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (204859752121/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (6447513/31250000:ℝ) + taylorErr ≤ (204859752121/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-248166536179/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-195758267101/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-204859752121/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-120888084931/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15829147750191/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (198928546049/12500000000:ℝ) := by nlinarith
  have hp1 : (26197217071337/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13169058637091/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-5395620176123/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-126677256091/40000000000:ℝ) := by nlinarith
  have hN : (2174265257559/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (101105770068913/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2174265257559/1000000000000:ℝ) (101105770068913/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (46245893/2500000000000:ℝ) ≤ ((2174265257559/1000000000000:ℝ)/(101105770068913/200000000000:ℝ))^2 := by norm_num
  linarith

end Zeta23Ext.Bridge.FourPoint
