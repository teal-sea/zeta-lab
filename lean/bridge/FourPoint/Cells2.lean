import FourPoint.Base

noncomputable section
open Real
namespace Zeta23Ext.Bridge.FourPoint


theorem wc_120 (x : ℝ) (h₁ : (2031/1024:ℝ) ≤ x) (h₂ : x ≤ (509/256:ℝ)) : (400103387/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (368155389/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (130388367/2500000000:ℝ) := by nlinarith
  have hc1 : (998640215917/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (998640215917/1000000000000:ℝ) ≤ taylorCos (130388367/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (999322386851/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (368155389/10000000000:ℝ) + taylorErr ≤ (999322386851/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (3680722067/100000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (3680722067/100000000000:ℝ) ≤ taylorSin (368155389/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (26065853477/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (130388367/2500000000:ℝ) + taylorErr ≤ (26065853477/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (998640215917/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999322386851/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-26065853477/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-3680722067/100000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6231029960391/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6246369768271/1000000000000:ℝ) := by nlinarith
  have hp1 : (2578086436277/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5168866622029/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-33682730003/62500000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-75913757093/200000000000:ℝ) := by nlinarith
  have hN : (689104500691/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (3851713528197/50000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (689104500691/500000000000:ℝ) (3851713528197/50000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (400103387/1250000000000:ℝ) ≤ ((689104500691/500000000000:ℝ)/(3851713528197/50000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_121 (x : ℝ) (h₁ : (16253/8192:ℝ) ≤ x) (h₂ : x ≤ (8129/4096:ℝ)) : (1902333181/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (120800987/2500000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (502378709/10000000000:ℝ) := by nlinarith
  have hc1 : (998738341287/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (998738341287/1000000000000:ℝ) ≤ taylorCos (502378709/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (998832799117/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (120800987/2500000000:ℝ) + taylorErr ≤ (998832799117/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (48301591169/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (48301591169/1000000000000:ℝ) ≤ taylorSin (120800987/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (2510837187/50000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (502378709/10000000000:ℝ) + taylorErr ≤ (2510837187/50000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (998738341287/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (998832799117/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-2510837187/50000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-48301591169/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (779118429547/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3117432456181/500000000000:ℝ) := by nlinarith
  have hp1 : (10315519165143/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5159346361797/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-518171148233/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-49825598941/100000000000:ℝ) := by nlinarith
  have hN : (1496994330697/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (38373540475403/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1496994330697/1000000000000:ℝ) (38373540475403/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1902333181/5000000000000:ℝ) ≤ ((1496994330697/1000000000000:ℝ)/(38373540475403/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_122 (x : ℝ) (h₁ : (8129/4096:ℝ) ≤ x) (h₂ : x ≤ (4067/2048:ℝ)) : (359863857/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (111213607/2500000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (483203949/10000000000:ℝ) := by nlinarith
  have hc1 : (998832794587/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (998832794587/1000000000000:ℝ) ≤ taylorCos (483203949/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (499505344059/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (111213607/2500000000:ℝ) + taylorErr ≤ (499505344059/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (5558846193/125000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (5558846193/125000000000:ℝ) ≤ taylorSin (111213607/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (48301595793/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (483203949/10000000000:ℝ) + taylorErr ≤ (48301595793/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (998832794587/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (499505344059/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-48301595793/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-5558846193/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6234864912361/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6238699864331/1000000000000:ℝ) := by nlinarith
  have hp1 : (5159346292589/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2581259890937/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-99743177511/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-9177603999/20000000000:ℝ) := by nlinarith
  have hN : (1457712994537/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (9605343999301/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1457712994537/1000000000000:ℝ) (9605343999301/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (359863857/1000000000000:ℝ) ≤ ((1457712994537/1000000000000:ℝ)/(9605343999301/125000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_123 (x : ℝ) (h₁ : (4067/2048:ℝ) ≤ x) (h₂ : x ≤ (8139/4096:ℝ)) : (339970037/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (101626227/2500000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (444854429/10000000000:ℝ) := by nlinarith
  have hc1 : (99901068359/100000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (99901068359/100000000000:ℝ) ≤ taylorCos (444854429/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (999173884831/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (101626227/2500000000:ℝ) + taylorErr ≤ (999173884831/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (8127858779/200000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (8127858779/200000000000:ℝ) ≤ taylorSin (101626227/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (5558846771/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (444854429/10000000000:ℝ) + taylorErr ≤ (5558846771/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (99901068359/100000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999173884831/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-5558846771/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-8127858779/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (623869986433/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6242534816301/1000000000000:ℝ) := by nlinarith
  have hp1 : (5162519712623/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10331386403903/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-459444751611/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-163907153/390625000:ℝ) := by nlinarith
  have hN : (141861299527/100000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (76938481865461/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (141861299527/100000000000:ℝ) (76938481865461/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (339970037/1000000000000:ℝ) ≤ ((141861299527/100000000000:ℝ)/(76938481865461/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_124 (x : ℝ) (h₁ : (4067/2048:ℝ) ≤ x) (h₂ : x ≤ (509/256:ℝ)) : (3204719257/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (368155389/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (444854429/10000000000:ℝ) := by nlinarith
  have hc1 : (99901068359/100000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (99901068359/100000000000:ℝ) ≤ taylorCos (444854429/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (999322386851/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (368155389/10000000000:ℝ) + taylorErr ≤ (999322386851/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (3680722067/100000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (3680722067/100000000000:ℝ) ≤ taylorSin (368155389/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (5558846771/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (444854429/10000000000:ℝ) + taylorErr ≤ (5558846771/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (99901068359/100000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999322386851/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-5558846771/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-3680722067/100000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (623869986433/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6246369768271/1000000000000:ℝ) := by nlinarith
  have hp1 : (5162519712623/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5168866622029/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-229863500253/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-380036004551/1000000000000:ℝ) := by nlinarith
  have hN : (1379046688141/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (3851713528197/50000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1379046688141/1000000000000:ℝ) (3851713528197/50000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (3204719257/10000000000000:ℝ) ≤ ((1379046688141/1000000000000:ℝ)/(3851713528197/50000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_125 (x : ℝ) (h₁ : (8139/4096:ℝ) ≤ x) (h₂ : x ≤ (509/256:ℝ)) : (3206563771/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (368155389/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (406504909/10000000000:ℝ) := by nlinarith
  have hc1 : (999173880303/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (999173880303/1000000000000:ℝ) ≤ taylorCos (406504909/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (999322386851/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (368155389/10000000000:ℝ) + taylorErr ≤ (999322386851/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (3680722067/100000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (3680722067/100000000000:ℝ) ≤ taylorSin (368155389/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (40639298519/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (406504909/10000000000:ℝ) + taylorErr ≤ (40639298519/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (999173880303/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999322386851/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-40639298519/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-3680722067/100000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (62425348163/10000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6246369768271/1000000000000:ℝ) := by nlinarith
  have hp1 : (2582846566329/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5168866622029/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-105029556829/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-190134807047/500000000000:ℝ) := by nlinarith
  have hN : (1379443494397/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (3851713528197/50000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1379443494397/1000000000000:ℝ) (3851713528197/50000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (3206563771/10000000000000:ℝ) ≤ ((1379443494397/1000000000000:ℝ)/(3851713528197/50000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_126 (x : ℝ) (h₁ : (509/256:ℝ) ≤ x) (h₂ : x ≤ (8149/4096:ℝ)) : (1509609143/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (329805869/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (36815539/1000000000:ℝ) := by nlinarith
  have hc1 : (999322382323/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (999322382323/1000000000000:ℝ) ≤ taylorCos (36815539/1000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (999456192001/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (329805869/10000000000:ℝ) + taylorErr ≤ (999456192001/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (32974606027/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (32974606027/1000000000000:ℝ) ≤ taylorSin (329805869/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (18403612647/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (36815539/1000000000:ℝ) + taylorErr ≤ (18403612647/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (999322382323/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999456192001/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-18403612647/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-32974606027/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (624636976827/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6250204720241/1000000000000:ℝ) := by nlinarith
  have hp1 : (5168866552693/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10344080084213/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-380736886119/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-170441338181/500000000000:ℝ) := by nlinarith
  have hN : (268041011737/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (38565059044923/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (268041011737/200000000000:ℝ) (38565059044923/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1509609143/5000000000000:ℝ) ≤ ((268041011737/200000000000:ℝ)/(38565059044923/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_127 (x : ℝ) (h₁ : (509/256:ℝ) ≤ x) (h₂ : x ≤ (4077/2048:ℝ)) : (2836262683/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (291456349/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (36815539/1000000000:ℝ) := by nlinarith
  have hc1 : (999322382323/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (999322382323/1000000000000:ℝ) ≤ taylorCos (36815539/1000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (999575298311/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (291456349/10000000000:ℝ) + taylorErr ≤ (999575298311/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (227668019/7812500000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (227668019/7812500000:ℝ) ≤ taylorSin (291456349/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (18403612647/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (36815539/1000000000:ℝ) + taylorErr ≤ (18403612647/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (999322382323/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999575298311/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-18403612647/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-227668019/7812500000:ℝ) := by rw [hsx]; linarith
  have hb1 : (624636976827/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (625403967221/100000000000:ℝ) := by nlinarith
  have hp1 : (5168866552693/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10350426924367/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-76194099139/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-150628557891/500000000000:ℝ) := by nlinarith
  have hN : (260115899621/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (38613012221577/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (260115899621/200000000000:ℝ) (38613012221577/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2836262683/10000000000000:ℝ) ≤ ((260115899621/200000000000:ℝ)/(38613012221577/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_128 (x : ℝ) (h₁ : (509/256:ℝ) ≤ x) (h₂ : x ≤ (2041/1024:ℝ)) : (248869577/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (21475731/1000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (36815539/1000000000:ℝ) := by nlinarith
  have hc1 : (999322382323/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (999322382323/1000000000000:ℝ) ≤ taylorCos (36815539/1000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (499884703807/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (21475731/1000000000:ℝ) + taylorErr ≤ (499884703807/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (21474077983/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (21474077983/1000000000000:ℝ) ≤ taylorSin (21475731/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (18403612647/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (36815539/1000000000:ℝ) + taylorErr ≤ (18403612647/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (999322382323/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (499884703807/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-18403612647/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-21474077983/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (624636976827/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (125234191523/20000000000:ℝ) := by nlinarith
  have hp1 : (5168866552693/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10363120604677/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-190718857423/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-27749160859/125000000000:ℝ) := by nlinarith
  have hN : (244263133839/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (38709006816049/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (244263133839/200000000000:ℝ) (38709006816049/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (248869577/1000000000000:ℝ) ≤ ((244263133839/200000000000:ℝ)/(38709006816049/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_129 (x : ℝ) (h₁ : (509/256:ℝ) ≤ x) (h₂ : x ≤ (1023/512:ℝ)) : (1865845891/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (61359231/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (36815539/1000000000:ℝ) := by nlinarith
  have hc1 : (999322382323/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (999322382323/1000000000000:ℝ) ≤ taylorCos (36815539/1000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (199996235509/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (61359231/10000000000:ℝ) + taylorErr ≤ (199996235509/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (1227176467/200000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (1227176467/200000000000:ℝ) ≤ taylorSin (61359231/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (18403612647/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (36815539/1000000000:ℝ) + taylorErr ≤ (18403612647/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (999322382323/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (199996235509/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-18403612647/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-1227176467/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (624636976827/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6277049384029/1000000000000:ℝ) := by nlinarith
  have hp1 : (5168866552693/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10388507965297/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-95593038287/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-12686222789/200000000000:ℝ) := by nlinarith
  have hN : (265688374067/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (38901348969539/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (265688374067/250000000000:ℝ) (38901348969539/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1865845891/10000000000000:ℝ) ≤ ((265688374067/250000000000:ℝ)/(38901348969539/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_130 (x : ℝ) (h₁ : (509/256:ℝ) ≤ x) (h₂ : x ≤ (2:ℝ)) : (410811713/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (36815539/1000000000:ℝ) := by nlinarith
  have hc1 : (999322382323/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (999322382323/1000000000000:ℝ) ≤ taylorCos (36815539/1000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (18403612647/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (36815539/1000000000:ℝ) + taylorErr ≤ (18403612647/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (999322382323/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (500000001131/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-18403612647/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1131/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (624636976827/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (314159265359/50000000000:ℝ) := by nlinarith
  have hp1 : (5168866552693/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10398662909543/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-95686482117/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (11761/500000000000:ℝ) := by nlinarith
  have hN : (999322358801/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (38978417604363/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (999322358801/1000000000000:ℝ) (38978417604363/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (410811713/2500000000000:ℝ) ≤ ((999322358801/1000000000000:ℝ)/(38978417604363/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_131 (x : ℝ) (h₁ : (8149/4096:ℝ) ≤ x) (h₂ : x ≤ (4077/2048:ℝ)) : (354706643/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (291456349/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (32980587/1000000000:ℝ) := by nlinarith
  have hc1 : (499728093737/500000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (499728093737/500000000000:ℝ) ≤ taylorCos (32980587/1000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (999575298311/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (291456349/10000000000:ℝ) + taylorErr ≤ (999575298311/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (227668019/7812500000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (227668019/7812500000:ℝ) ≤ taylorSin (291456349/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (32974610651/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (32980587/1000000000:ℝ) + taylorErr ≤ (32974610651/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (499728093737/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999575298311/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-32974610651/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-227668019/7812500000:ℝ) := by rw [hsx]; linarith
  have hb1 : (78127559003/12500000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (625403967221/100000000000:ℝ) := by nlinarith
  have hp1 : (646504996591/62500000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10350426924367/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-341301297903/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-301442072263/1000000000000:ℝ) := by nlinarith
  have hN : (1300898259737/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (38613012221577/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1300898259737/1000000000000:ℝ) (38613012221577/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (354706643/1250000000000:ℝ) ≤ ((1300898259737/1000000000000:ℝ)/(38613012221577/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_132 (x : ℝ) (h₁ : (4077/2048:ℝ) ≤ x) (h₂ : x ≤ (8159/4096:ℝ)) : (2661857281/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (25310683/1000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (5829127/200000000:ℝ) := by nlinarith
  have hc1 : (124946911723/125000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (124946911723/125000000000:ℝ) ≤ taylorCos (5829127/200000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (39987188161/40000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (25310683/1000000000:ℝ) + taylorErr ≤ (39987188161/40000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (12653989179/500000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (12653989179/500000000000:ℝ) ≤ taylorSin (25310683/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (29141511057/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (5829127/200000000:ℝ) + taylorErr ≤ (29141511057/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (124946911723/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (39987188161/40000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-29141511057/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-12653989179/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6254039672209/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (312893731209/50000000000:ℝ) := by nlinarith
  have hp1 : (414017071421/40000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5178386882261/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-150906018587/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-65487094271/250000000000:ℝ) := by nlinarith
  have hN : (315380917717/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (9665248702989/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (315380917717/250000000000:ℝ) (9665248702989/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2661857281/10000000000000:ℝ) ≤ ((315380917717/250000000000:ℝ)/(9665248702989/125000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_133 (x : ℝ) (h₁ : (4077/2048:ℝ) ≤ x) (h₂ : x ≤ (2041/1024:ℝ)) : (1245418929/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (21475731/1000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (5829127/200000000:ℝ) := by nlinarith
  have hc1 : (124946911723/125000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (124946911723/125000000000:ℝ) ≤ taylorCos (5829127/200000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (499884703807/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (21475731/1000000000:ℝ) + taylorErr ≤ (499884703807/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (21474077983/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (21474077983/1000000000000:ℝ) ≤ taylorSin (21475731/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (29141511057/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (5829127/200000000:ℝ) + taylorErr ≤ (29141511057/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (124946911723/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (499884703807/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-29141511057/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-21474077983/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6254039672209/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (125234191523/20000000000:ℝ) := by nlinarith
  have hp1 : (414017071421/40000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10363120604677/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-301996993687/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-222265871949/1000000000000:ℝ) := by nlinarith
  have hN : (1221841165733/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (38709006816049/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1221841165733/1000000000000:ℝ) (38709006816049/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1245418929/5000000000000:ℝ) ≤ ((1221841165733/1000000000000:ℝ)/(38709006816049/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_134 (x : ℝ) (h₁ : (8159/4096:ℝ) ≤ x) (h₂ : x ≤ (2041/1024:ℝ)) : (1245909663/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (21475731/1000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (253106831/10000000000:ℝ) := by nlinarith
  have hc1 : (499839849749/500000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (499839849749/500000000000:ℝ) ≤ taylorCos (253106831/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (499884703807/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (21475731/1000000000:ℝ) + taylorErr ≤ (499884703807/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (21474077983/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (21474077983/1000000000000:ℝ) ≤ taylorSin (21475731/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (12653991491/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (253106831/10000000000:ℝ) + taylorErr ≤ (12653991491/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (499839849749/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (499884703807/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-12653991491/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-21474077983/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6257874624179/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (125234191523/20000000000:ℝ) := by nlinarith
  have hp1 : (2071354725119/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10363120604677/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-8195927497/31250000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-27800270561/125000000000:ℝ) := by nlinarith
  have hN : (611040931993/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (38709006816049/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (611040931993/500000000000:ℝ) (38709006816049/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1245909663/5000000000000:ℝ) ≤ ((611040931993/500000000000:ℝ)/(38709006816049/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_135 (x : ℝ) (h₁ : (2041/1024:ℝ) ≤ x) (h₂ : x ≤ (4087/2048:ℝ)) : (1084176557/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (13805827/1000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (214757311/10000000000:ℝ) := by nlinarith
  have hc1 : (62485587693/62500000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (62485587693/62500000000:ℝ) ≤ taylorCos (214757311/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (499952351673/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (13805827/1000000000:ℝ) + taylorErr ≤ (499952351673/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (552215447/40000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (552215447/40000000000:ℝ) ≤ taylorSin (13805827/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (21474082607/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (214757311/10000000000:ℝ) + taylorErr ≤ (21474082607/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (62485587693/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (499952351673/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-21474082607/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-552215447/40000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6261709576149/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6269379480089/1000000000000:ℝ) := by nlinarith
  have hp1 : (2072624093133/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5187907142493/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-222811093071/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-71533440003/500000000000:ℝ) := by nlinarith
  have hN : (571418141547/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (77610238130723/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (571418141547/500000000000:ℝ) (77610238130723/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1084176557/5000000000000:ℝ) ≤ ((571418141547/500000000000:ℝ)/(77610238130723/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_136 (x : ℝ) (h₁ : (2041/1024:ℝ) ≤ x) (h₂ : x ≤ (1023/512:ℝ)) : (1867963109/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (61359231/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (214757311/10000000000:ℝ) := by nlinarith
  have hc1 : (62485587693/62500000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (62485587693/62500000000:ℝ) ≤ taylorCos (214757311/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (199996235509/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (61359231/10000000000:ℝ) + taylorErr ≤ (199996235509/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (1227176467/200000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (1227176467/200000000000:ℝ) ≤ taylorSin (61359231/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (21474082607/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (214757311/10000000000:ℝ) + taylorErr ≤ (21474082607/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (62485587693/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (199996235509/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-21474082607/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-1227176467/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6261709576149/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6277049384029/1000000000000:ℝ) := by nlinarith
  have hp1 : (2072624093133/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10388507965297/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-223083678211/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-317934439/5000000000:ℝ) := by nlinarith
  have hN : (132919536361/125000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (38901348969539/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (132919536361/125000000000:ℝ) (38901348969539/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1867963109/10000000000000:ℝ) ≤ ((132919536361/125000000000:ℝ)/(38901348969539/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_137 (x : ℝ) (h₁ : (4087/2048:ℝ) ≤ x) (h₂ : x ≤ (1023/512:ℝ)) : (1868712167/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (61359231/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (138058271/10000000000:ℝ) := by nlinarith
  have hc1 : (999904698821/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (999904698821/1000000000000:ℝ) ≤ taylorCos (138058271/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (199996235509/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (61359231/10000000000:ℝ) + taylorErr ≤ (199996235509/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (1227176467/200000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (1227176467/200000000000:ℝ) ≤ taylorSin (61359231/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (13805390799/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (138058271/10000000000:ℝ) + taylorErr ≤ (13805390799/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (999904698821/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (199996235509/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-13805390799/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-1227176467/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (783672435011/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6277049384029/1000000000000:ℝ) := by nlinarith
  have hp1 : (10375814145803/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10388507965297/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-3585435307/25000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-7958096841/125000000000:ℝ) := by nlinarith
  have hN : (1063569473549/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (38901348969539/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1063569473549/1000000000000:ℝ) (38901348969539/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1868712167/10000000000000:ℝ) ≤ ((1063569473549/1000000000000:ℝ)/(38901348969539/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_138 (x : ℝ) (h₁ : (1023/512:ℝ) ≤ x) (h₂ : x ≤ (2:ℝ)) : (822707073/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (479369/78125000:ℝ) := by nlinarith
  have hc1 : (49999058651/50000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (49999058651/50000000000:ℝ) ≤ taylorCos (479369/78125000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (76698587/12500000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (479369/78125000:ℝ) + taylorErr ≤ (76698587/12500000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (49999058651/50000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (500000001131/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-76698587/12500000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1131/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1569262346007/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (314159265359/50000000000:ℝ) := by nlinarith
  have hp1 : (1298563478243/125000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10398662909543/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-63805020149/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (11761/500000000000:ℝ) := by nlinarith
  have hN : (499990574749/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (38978417604363/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (499990574749/500000000000:ℝ) (38978417604363/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (822707073/5000000000000:ℝ) ≤ ((499990574749/500000000000:ℝ)/(38978417604363/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_139 (x : ℝ) (h₁ : (2:ℝ) ≤ x) (h₂ : x ≤ (4097/2048:ℝ)) : (1591808227/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (479369/312500000:ℝ) := by nlinarith
  have hc1 : (99999882119/100000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (99999882119/100000000000:ℝ) ≤ taylorCos (479369/312500000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (1533982461/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (479369/312500000:ℝ) + taylorErr ≤ (1533982461/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (99999882119/100000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (500000001131/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1533982461/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6283185307179/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (196397477749/31250000000:ℝ) := by nlinarith
  have hp1 : (5199331385027/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5200600822803/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2941/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (7977630449/500000000000:ℝ) := by nlinarith
  have hN : (246010890073/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (15599078611423/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (246010890073/250000000000:ℝ) (15599078611423/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1591808227/10000000000000:ℝ) ≤ ((246010890073/250000000000:ℝ)/(15599078611423/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_140 (x : ℝ) (h₁ : (2:ℝ) ≤ x) (h₂ : x ≤ (2051/1024:ℝ)) : (1337086167/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (1438107/156250000:ℝ) := by nlinarith
  have hc1 : (999957642289/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (999957642289/1000000000000:ℝ) ≤ taylorCos (1438107/156250000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (9203757117/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1438107/156250000:ℝ) + taylorErr ≤ (9203757117/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (999957642289/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (500000001131/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (9203757117/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6283185307179/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6292389191907/1000000000000:ℝ) := by nlinarith
  have hp1 : (5199331385027/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5206947662957/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-23557/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (47923481611/500000000000:ℝ) := by nlinarith
  have hN : (904110679067/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (78188323484857/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (904110679067/1000000000000:ℝ) (78188323484857/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1337086167/10000000000000:ℝ) ≤ ((904110679067/1000000000000:ℝ)/(78188323484857/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_141 (x : ℝ) (h₁ : (2:ℝ) ≤ x) (h₂ : x ≤ (257/128:ℝ)) : (179073511/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (245436927/10000000000:ℝ) := by nlinarith
  have hc1 : (62481176027/62500000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (62481176027/62500000000:ℝ) ≤ taylorCos (245436927/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (24541230879/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (245436927/10000000000:ℝ) + taylorErr ≤ (24541230879/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (62481176027/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (500000001131/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (24541230879/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6283185307179/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3153864499893/500000000000:ℝ) := by nlinarith
  have hp1 : (5199331385027/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5219641343267/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-11807/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (128096423311/500000000000:ℝ) := by nlinarith
  have hN : (74350596981/100000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (78574890269483/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (74350596981/100000000000:ℝ) (78574890269483/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (179073511/2000000000000:ℝ) ≤ ((74350596981/100000000000:ℝ)/(78574890269483/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_142 (x : ℝ) (h₁ : (4097/2048:ℝ) ≤ x) (h₂ : x ≤ (2051/1024:ℝ)) : (1337086167/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (15339807/10000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (1438107/156250000:ℝ) := by nlinarith
  have hc1 : (999957642289/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (999957642289/1000000000000:ℝ) ≤ taylorCos (1438107/156250000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (499999412857/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (15339807/10000000000:ℝ) + taylorErr ≤ (499999412857/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (383494459/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (383494459/250000000000:ℝ) ≤ taylorSin (15339807/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (9203757117/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1438107/156250000:ℝ) + taylorErr ≤ (9203757117/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (999957642289/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (499999412857/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (383494459/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (9203757117/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6284719287967/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6292389191907/1000000000000:ℝ) := by nlinarith
  have hp1 : (5200600753041/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5206947662957/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (7977606289/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (47923481611/500000000000:ℝ) := by nlinarith
  have hN : (904110679067/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (78188323484857/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (904110679067/1000000000000:ℝ) (78188323484857/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1337086167/10000000000000:ℝ) ≤ ((904110679067/1000000000000:ℝ)/(78188323484857/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_143 (x : ℝ) (h₁ : (2051/1024:ℝ) ≤ x) (h₂ : x ≤ (257/128:ℝ)) : (179073511/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (92038847/10000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (245436927/10000000000:ℝ) := by nlinarith
  have hc1 : (62481176027/62500000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (62481176027/62500000000:ℝ) ≤ taylorCos (245436927/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (499978823407/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (92038847/10000000000:ℝ) + taylorErr ≤ (499978823407/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (9203752493/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (9203752493/1000000000000:ℝ) ≤ taylorSin (92038847/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (24541230879/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (245436927/10000000000:ℝ) + taylorErr ≤ (24541230879/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (62481176027/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (499978823407/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (9203752493/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (24541230879/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3146194595953/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3153864499893/500000000000:ℝ) := by nlinarith
  have hp1 : (10413895186221/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5219641343267/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (47923456891/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (128096423311/500000000000:ℝ) := by nlinarith
  have hN : (74350596981/100000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (78574890269483/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (74350596981/100000000000:ℝ) (78574890269483/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (179073511/2000000000000:ℝ) ≤ ((74350596981/100000000000:ℝ)/(78574890269483/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_144 (x : ℝ) (h₁ : (257/128:ℝ) ≤ x) (h₂ : x ≤ (2061/1024:ℝ)) : (543159341/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/5000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (79767001/2000000000:ℝ) := by nlinarith
  have hc1 : (249801189089/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (249801189089/250000000000:ℝ) ≤ taylorCos (79767001/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (999698820959/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/5000000000:ℝ) + taylorErr ≤ (999698820959/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (4908245251/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (4908245251/200000000000:ℝ) ≤ taylorSin (122718463/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (7974585973/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (79767001/2000000000:ℝ) + taylorErr ≤ (7974585973/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (249801189089/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999698820959/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (4908245251/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (7974585973/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1261545799957/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1264613761533/200000000000:ℝ) := by nlinarith
  have hp1 : (10439282546499/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10464670047153/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (256192794913/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (417257054851/1000000000000:ℝ) := by nlinarith
  have hN : (116389540301/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (78962398292933/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (116389540301/200000000000:ℝ) (78962398292933/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (543159341/10000000000000:ℝ) ≤ ((116389540301/200000000000:ℝ)/(78962398292933/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_145 (x : ℝ) (h₁ : (257/128:ℝ) ≤ x) (h₂ : x ≤ (1033/512:ℝ)) : (27945219/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/5000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (138058271/2500000000:ℝ) := by nlinarith
  have hc1 : (998475578309/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (998475578309/1000000000000:ℝ) ≤ taylorCos (138058271/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (999698820959/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/5000000000:ℝ) + taylorErr ≤ (999698820959/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (4908245251/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (4908245251/200000000000:ℝ) ≤ taylorSin (122718463/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (6899405831/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (138058271/2500000000:ℝ) + taylorErr ≤ (6899405831/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (998475578309/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999698820959/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (4908245251/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (6899405831/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1261545799957/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (792301076943/125000000000:ℝ) := by nlinarith
  have hp1 : (10439282546499/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2622514351943/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (256192794913/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (289500652987/500000000000:ℝ) := by nlinarith
  have hN : (83894854467/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (15870169511041/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (83894854467/200000000000:ℝ) (15870169511041/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (27945219/1000000000000:ℝ) ≤ ((83894854467/200000000000:ℝ)/(15870169511041/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_146 (x : ℝ) (h₁ : (257/128:ℝ) ≤ x) (h₂ : x ≤ (519/256:ℝ)) : (13164037/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/5000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (429514621/5000000000:ℝ) := by nlinarith
  have hc1 : (498156304957/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (498156304957/500000000000:ℝ) ≤ taylorCos (429514621/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (999698820959/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/5000000000:ℝ) + taylorErr ≤ (999698820959/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (4908245251/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (4908245251/200000000000:ℝ) ≤ taylorSin (122718463/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (17159462937/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (429514621/5000000000:ℝ) + taylorErr ≤ (17159462937/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (498156304957/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999698820959/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (4908245251/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (17159462937/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1261545799957/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3184544115651/500000000000:ℝ) := by nlinarith
  have hp1 : (10439282546499/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10540832129011/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (256192794913/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (180875018243/200000000000:ℝ) := by nlinarith
  have hN : (91937518699/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (4006528489811/50000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (91937518699/1000000000000:ℝ) (4006528489811/50000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (13164037/10000000000000:ℝ) ≤ ((91937518699/1000000000000:ℝ)/(4006528489811/50000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_147 (x : ℝ) (h₁ : (2061/1024:ℝ) ≤ x) (h₂ : x ≤ (1033/512:ℝ)) : (27945219/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (99708751/2500000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (138058271/2500000000:ℝ) := by nlinarith
  have hc1 : (998475578309/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (998475578309/1000000000000:ℝ) ≤ taylorCos (138058271/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (249801190221/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (99708751/2500000000:ℝ) + taylorErr ≤ (249801190221/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (39872925241/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (39872925241/1000000000000:ℝ) ≤ taylorSin (99708751/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (6899405831/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (138058271/2500000000:ℝ) + taylorErr ≤ (6899405831/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (998475578309/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (249801190221/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (39872925241/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (6899405831/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (395191800479/62500000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (792301076943/125000000000:ℝ) := by nlinarith
  have hp1 : (5232334953389/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2622514351943/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (13039281277/31250000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (289500652987/500000000000:ℝ) := by nlinarith
  have hN : (83894854467/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (15870169511041/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (83894854467/200000000000:ℝ) (15870169511041/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (27945219/1000000000000:ℝ) ≤ ((83894854467/200000000000:ℝ)/(15870169511041/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_148 (x : ℝ) (h₁ : (1033/512:ℝ) ≤ x) (h₂ : x ≤ (2071/1024:ℝ)) : (103168503/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (552233083/10000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (705631163/10000000000:ℝ) := by nlinarith
  have hc1 : (498755726937/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (498755726937/500000000000:ℝ) ≤ taylorCos (705631163/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (998475582839/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (552233083/10000000000:ℝ) + taylorErr ≤ (998475582839/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (6899405253/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (6899405253/125000000000:ℝ) ≤ taylorSin (552233083/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (70504575709/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (705631163/10000000000:ℝ) + taylorErr ≤ (70504575709/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (498755726937/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (998475582839/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (6899405253/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (70504575709/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6338408615543/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6353748423423/1000000000000:ℝ) := by nlinarith
  have hp1 : (10490057267057/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10515444768391/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (5790012497/10000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (741386971787/1000000000000:ℝ) := by nlinarith
  have hN : (256124482087/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (79740238056301/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (256124482087/1000000000000:ℝ) (79740238056301/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (103168503/10000000000000:ℝ) ≤ ((256124482087/1000000000000:ℝ)/(79740238056301/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_149 (x : ℝ) (h₁ : (1033/512:ℝ) ≤ x) (h₂ : x ≤ (519/256:ℝ)) : (13164037/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (552233083/10000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (429514621/5000000000:ℝ) := by nlinarith
  have hc1 : (498156304957/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (498156304957/500000000000:ℝ) ≤ taylorCos (429514621/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (998475582839/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (552233083/10000000000:ℝ) + taylorErr ≤ (998475582839/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (6899405253/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (6899405253/125000000000:ℝ) ≤ taylorSin (552233083/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (17159462937/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (429514621/5000000000:ℝ) + taylorErr ≤ (17159462937/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (498156304957/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (998475582839/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (6899405253/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (17159462937/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6338408615543/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3184544115651/500000000000:ℝ) := by nlinarith
  have hp1 : (10490057267057/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10540832129011/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (5790012497/10000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (180875018243/200000000000:ℝ) := by nlinarith
  have hN : (91937518699/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (4006528489811/50000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (91937518699/1000000000000:ℝ) (4006528489811/50000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (13164037/10000000000000:ℝ) ≤ ((91937518699/1000000000000:ℝ)/(4006528489811/50000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_150 (x : ℝ) (h₁ : (2071/1024:ℝ) ≤ x) (h₂ : x ≤ (519/256:ℝ)) : (13164037/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (352815581/5000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (429514621/5000000000:ℝ) := by nlinarith
  have hc1 : (498156304957/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (498156304957/500000000000:ℝ) ≤ taylorCos (429514621/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (199502291681/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (352815581/5000000000:ℝ) + taylorErr ≤ (199502291681/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (14100914217/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (14100914217/200000000000:ℝ) ≤ taylorSin (352815581/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (17159462937/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (429514621/5000000000:ℝ) + taylorErr ≤ (17159462937/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (498156304957/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (199502291681/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (14100914217/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (17159462937/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3176874211711/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3184544115651/500000000000:ℝ) := by nlinarith
  have hp1 : (2103088925467/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10540832129011/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (370693456609/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (180875018243/200000000000:ℝ) := by nlinarith
  have hN : (91937518699/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (4006528489811/50000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (91937518699/1000000000000:ℝ) (4006528489811/50000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (13164037/10000000000000:ℝ) ≤ ((91937518699/1000000000000:ℝ)/(4006528489811/50000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_151 (x : ℝ) (h₁ : (1043/512:ℝ) ≤ x) (h₂ : x ≤ (131/64:ℝ)) : (21355581/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (582912699/5000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (1472621557/10000000000:ℝ) := by nlinarith
  have hc1 : (989176507693/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (989176507693/1000000000000:ℝ) ≤ taylorCos (1472621557/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (496605975753/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (582912699/5000000000:ℝ) + taylorErr ≤ (496605975753/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (116318628571/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (116318628571/1000000000000:ℝ) ≤ taylorSin (582912699/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (7336523839/50000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1472621557/10000000000:ℝ) + taylorErr ≤ (7336523839/50000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (989176507693/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (496605975753/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (116318628571/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (7336523839/50000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3199883923529/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6430447462817/1000000000000:ℝ) := by nlinarith
  have hp1 : (1059160670817/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5321190785743/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1232001166657/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1561561722059/1000000000000:ℝ) := by nlinarith
  have hN : (238789215151/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (817013091441/10000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (238789215151/1000000000000:ℝ) (817013091441/10000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (21355581/2500000000000:ℝ) ≤ ((238789215151/1000000000000:ℝ)/(817013091441/10000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_152 (x : ℝ) (h₁ : (1043/512:ℝ) ≤ x) (h₂ : x ≤ (1053/512:ℝ)) : (83791953/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (582912699/5000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (889708857/5000000000:ℝ) := by nlinarith
  have hc1 : (246052522531/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (246052522531/250000000000:ℝ) ≤ taylorCos (889708857/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (496605975753/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (582912699/5000000000:ℝ) + taylorErr ≤ (496605975753/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (116318628571/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (116318628571/1000000000000:ℝ) ≤ taylorSin (582912699/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (177004222679/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (889708857/5000000000:ℝ) + taylorErr ≤ (177004222679/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (246052522531/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (496605975753/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (116318628571/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (177004222679/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3199883923529/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (258445083143/40000000000:ℝ) := by nlinarith
  have hp1 : (1059160670817/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2673289073181/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1232001166657/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1892733817579/1000000000000:ℝ) := by nlinarith
  have hN : (238789215151/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (82492326250991/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (238789215151/1000000000000:ℝ) (82492326250991/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (83791953/10000000000000:ℝ) ≤ ((238789215151/1000000000000:ℝ)/(82492326250991/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_153 (x : ℝ) (h₁ : (1043/512:ℝ) ≤ x) (h₂ : x ≤ (529/256:ℝ)) : (1284381/156250000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (582912699/5000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (130388367/625000000:ℝ) := by nlinarith
  have hc1 : (7643104441/7812500000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (7643104441/7812500000:ℝ) ≤ taylorCos (130388367/625000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (496605975753/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (582912699/5000000000:ℝ) + taylorErr ≤ (496605975753/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (116318628571/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (116318628571/1000000000000:ℝ) ≤ taylorSin (582912699/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (207111378501/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (130388367/625000000:ℝ) + taylorErr ≤ (207111378501/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (7643104441/7812500000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (496605975753/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (116318628571/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (207111378501/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3199883923529/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6491806694333/1000000000000:ℝ) := by nlinarith
  have hp1 : (1059160670817/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10743931013963/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1232001166657/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1112595181411/500000000000:ℝ) := by nlinarith
  have hN : (238789215151/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (41643554156587/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (238789215151/1000000000000:ℝ) (41643554156587/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1284381/156250000000:ℝ) ≤ ((238789215151/1000000000000:ℝ)/(41643554156587/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_154 (x : ℝ) (h₁ : (131/64:ℝ) ≤ x) (h₂ : x ≤ (529/256:ℝ)) : (94460693/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (368155389/2500000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (130388367/625000000:ℝ) := by nlinarith
  have hc1 : (7643104441/7812500000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (7643104441/7812500000:ℝ) ≤ taylorCos (130388367/625000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (123647064029/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (368155389/2500000000:ℝ) + taylorErr ≤ (123647064029/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (146730472157/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (146730472157/1000000000000:ℝ) ≤ taylorSin (368155389/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (207111378501/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (130388367/625000000:ℝ) + taylorErr ≤ (207111378501/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (7643104441/7812500000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (123647064029/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (146730472157/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (207111378501/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (200951483213/31250000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6491806694333/1000000000000:ℝ) := by nlinarith
  have hp1 : (10642381428727/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10743931013963/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (195195206489/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1112595181411/500000000000:ℝ) := by nlinarith
  have hN : (3577407123/6250000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (41643554156587/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3577407123/6250000000:ℝ) (41643554156587/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (94460693/2000000000000:ℝ) ≤ ((3577407123/6250000000:ℝ)/(41643554156587/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_155 (x : ℝ) (h₁ : (131/64:ℝ) ≤ x) (h₂ : x ≤ (1063/512:ℝ)) : (115843823/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (368155389/2500000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (239301003/1000000000:ℝ) := by nlinarith
  have hc1 : (971503888703/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (971503888703/1000000000000:ℝ) ≤ taylorCos (239301003/1000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (123647064029/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (368155389/2500000000:ℝ) + taylorErr ≤ (123647064029/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (146730472157/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (146730472157/1000000000000:ℝ) ≤ taylorSin (368155389/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (29627951043/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (239301003/1000000000:ℝ) + taylorErr ≤ (29627951043/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (971503888703/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (123647064029/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (146730472157/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (29627951043/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (200951483213/31250000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (652248631009/100000000000:ℝ) := by nlinarith
  have hp1 : (10642381428727/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13493382169/1250000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (195195206489/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (2558600104369/1000000000000:ℝ) := by nlinarith
  have hN : (3577407123/6250000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (84085655330623/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3577407123/6250000000:ℝ) (84085655330623/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (115843823/2500000000000:ℝ) ≤ ((3577407123/6250000000:ℝ)/(84085655330623/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_156 (x : ℝ) (h₁ : (131/64:ℝ) ≤ x) (h₂ : x ≤ (267/128:ℝ)) : (18186303/400000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (368155389/2500000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (2699806187/10000000000:ℝ) := by nlinarith
  have hc1 : (38551042541/40000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (38551042541/40000000000:ℝ) ≤ taylorCos (2699806187/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (123647064029/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (368155389/2500000000:ℝ) + taylorErr ≤ (123647064029/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (146730472157/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (146730472157/1000000000000:ℝ) ≤ taylorSin (368155389/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (33339094971/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2699806187/10000000000:ℝ) + taylorErr ≤ (33339094971/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (38551042541/40000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (123647064029/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (146730472157/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (33339094971/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (200951483213/31250000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (819145740731/125000000000:ℝ) := by nlinarith
  have hp1 : (10642381428727/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5422740228219/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (195195206489/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (2892628023547/1000000000000:ℝ) := by nlinarith
  have hN : (3577407123/6250000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (84887967303391/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3577407123/6250000000:ℝ) (84887967303391/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (18186303/400000000000:ℝ) ≤ ((3577407123/6250000000:ℝ)/(84887967303391/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_157 (x : ℝ) (h₁ : (131/64:ℝ) ≤ x) (h₂ : x ≤ (539/256:ℝ)) : (437829947/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (368155389/2500000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (1656699251/5000000000:ℝ) := by nlinarith
  have hc1 : (945607323113/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (945607323113/1000000000000:ℝ) ≤ taylorCos (1656699251/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (123647064029/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (368155389/2500000000:ℝ) + taylorErr ≤ (123647064029/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (146730472157/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (146730472157/1000000000000:ℝ) ≤ taylorSin (368155389/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (8132757361/25000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1656699251/5000000000:ℝ) + taylorErr ≤ (8132757361/25000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (945607323113/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (123647064029/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (146730472157/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (8132757361/25000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (200951483213/31250000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6614525157363/1000000000000:ℝ) := by nlinarith
  have hp1 : (10642381428727/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10947029898913/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (195195206489/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (3561181519659/1000000000000:ℝ) := by nlinarith
  have hN : (3577407123/6250000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (86503886114777/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3577407123/6250000000:ℝ) (86503886114777/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (437829947/10000000000000:ℝ) ≤ ((3577407123/6250000000:ℝ)/(86503886114777/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_158 (x : ℝ) (h₁ : (131/64:ℝ) ≤ x) (h₂ : x ≤ (17/8:ℝ)) : (42177537/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (368155389/2500000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (3926990817/10000000000:ℝ) := by nlinarith
  have hc1 : (923879530249/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (923879530249/1000000000000:ℝ) ≤ taylorCos (3926990817/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (123647064029/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (368155389/2500000000:ℝ) + taylorErr ≤ (123647064029/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (146730472157/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (146730472157/1000000000000:ℝ) ≤ taylorSin (368155389/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (95670858657/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/10000000000:ℝ) + taylorErr ≤ (95670858657/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (923879530249/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (123647064029/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (146730472157/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (95670858657/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (200951483213/31250000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6675884388879/1000000000000:ℝ) := by nlinarith
  have hp1 : (10642381428727/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1104857934139/100000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (195195206489/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1057027072531/250000000000:ℝ) := by nlinarith
  have hN : (3577407123/6250000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (88134864747357/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3577407123/6250000000:ℝ) (88134864747357/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (42177537/1000000000000:ℝ) ≤ ((3577407123/6250000000:ℝ)/(88134864747357/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_159 (x : ℝ) (h₁ : (131/64:ℝ) ≤ x) (h₂ : x ≤ (277/128:ℝ)) : (12244337/312500000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (368155389/2500000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (644271931/1250000000:ℝ) := by nlinarith
  have hc1 : (870086988811/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (870086988811/1000000000000:ℝ) ≤ taylorCos (644271931/1250000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (123647064029/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (368155389/2500000000:ℝ) + taylorErr ≤ (123647064029/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (146730472157/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (146730472157/1000000000000:ℝ) ≤ taylorSin (368155389/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (492898194553/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (644271931/1250000000:ℝ) + taylorErr ≤ (492898194553/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (870086988811/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (123647064029/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (146730472157/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (492898194553/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (200951483213/31250000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (679860285191/100000000000:ℝ) := by nlinarith
  have hp1 : (10642381428727/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (11251678226343/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (195195206489/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (86655185679/15625000000:ℝ) := by nlinarith
  have hN : (3577407123/6250000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (45721000737999/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3577407123/6250000000:ℝ) (45721000737999/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (12244337/312500000000:ℝ) ≤ ((3577407123/6250000000:ℝ)/(45721000737999/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_160 (x : ℝ) (h₁ : (131/64:ℝ) ≤ x) (h₂ : x ≤ (141/64:ℝ)) : (182240171/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (368155389/2500000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (3190680039/5000000000:ℝ) := by nlinarith
  have hc1 : (160641505837/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (160641505837/200000000000:ℝ) ≤ taylorCos (3190680039/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (123647064029/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (368155389/2500000000:ℝ) + taylorErr ≤ (123647064029/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (146730472157/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (146730472157/1000000000000:ℝ) ≤ taylorSin (368155389/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (297849653393/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3190680039/5000000000:ℝ) + taylorErr ≤ (297849653393/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (160641505837/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (123647064029/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (146730472157/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (297849653393/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (200951483213/31250000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6921321314941/1000000000000:ℝ) := by nlinarith
  have hp1 : (10642381428727/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2290955422259/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (195195206489/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (6823602784587/1000000000000:ℝ) := by nlinarith
  have hN : (3577407123/6250000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (47404688744657/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3577407123/6250000000:ℝ) (47404688744657/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (182240171/5000000000000:ℝ) ≤ ((3577407123/6250000000:ℝ)/(47404688744657/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_161 (x : ℝ) (h₁ : (131/64:ℝ) ≤ x) (h₂ : x ≤ (9/4:ℝ)) : (167375901/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (368155389/2500000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (123647064029/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (368155389/2500000000:ℝ) + taylorErr ≤ (123647064029/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (146730472157/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (146730472157/1000000000000:ℝ) ≤ taylorSin (368155389/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (176776695861/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/5000000000:ℝ) + taylorErr ≤ (176776695861/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (123647064029/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (146730472157/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (176776695861/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (200951483213/31250000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3534291735289/500000000000:ℝ) := by nlinarith
  have hp1 : (10642381428727/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (11698495773237/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (195195206489/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (8272085717347/1000000000000:ℝ) := by nlinarith
  have hN : (3577407123/6250000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (49464872280529/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3577407123/6250000000:ℝ) (49464872280529/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (167375901/5000000000000:ℝ) ≤ ((3577407123/6250000000:ℝ)/(49464872280529/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_162 (x : ℝ) (h₁ : (1053/512:ℝ) ≤ x) (h₂ : x ≤ (1063/512:ℝ)) : (291856019/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1779417713/10000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (239301003/1000000000:ℝ) := by nlinarith
  have hc1 : (971503888703/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (971503888703/1000000000000:ℝ) ≤ taylorCos (239301003/1000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (492105047333/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1779417713/10000000000:ℝ) + taylorErr ≤ (492105047333/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (177004218057/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (177004218057/1000000000000:ℝ) ≤ taylorSin (1779417713/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (29627951043/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (239301003/1000000000:ℝ) + taylorErr ≤ (29627951043/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (971503888703/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (492105047333/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (177004218057/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (29627951043/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3230563539287/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (652248631009/100000000000:ℝ) := by nlinarith
  have hp1 : (2138631229857/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13493382169/1250000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (378546748553/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (2558600104369/1000000000000:ℝ) := by nlinarith
  have hN : (908523648099/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (84085655330623/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (908523648099/1000000000000:ℝ) (84085655330623/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (291856019/2500000000000:ℝ) ≤ ((908523648099/1000000000000:ℝ)/(84085655330623/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_163 (x : ℝ) (h₁ : (1053/512:ℝ) ≤ x) (h₂ : x ≤ (267/128:ℝ)) : (1145460727/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1779417713/10000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (2699806187/10000000000:ℝ) := by nlinarith
  have hc1 : (38551042541/40000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (38551042541/40000000000:ℝ) ≤ taylorCos (2699806187/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (492105047333/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1779417713/10000000000:ℝ) + taylorErr ≤ (492105047333/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (177004218057/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (177004218057/1000000000000:ℝ) ≤ taylorSin (1779417713/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (33339094971/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2699806187/10000000000:ℝ) + taylorErr ≤ (33339094971/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (38551042541/40000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (492105047333/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (177004218057/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (33339094971/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3230563539287/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (819145740731/125000000000:ℝ) := by nlinarith
  have hp1 : (2138631229857/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5422740228219/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (378546748553/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (2892628023547/1000000000000:ℝ) := by nlinarith
  have hN : (908523648099/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (84887967303391/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (908523648099/1000000000000:ℝ) (84887967303391/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1145460727/10000000000000:ℝ) ≤ ((908523648099/1000000000000:ℝ)/(84887967303391/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_164 (x : ℝ) (h₁ : (529/256:ℝ) ≤ x) (h₂ : x ≤ (2131/1024:ℝ)) : (54451693/250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2086213871/10000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (636602027/2500000000:ℝ) := by nlinarith
  have hc1 : (967753834829/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (967753834829/1000000000000:ℝ) ≤ taylorCos (636602027/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (978317372993/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2086213871/10000000000:ℝ) + taylorErr ≤ (978317372993/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (207111373879/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (207111373879/1000000000000:ℝ) ≤ taylorSin (2086213871/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (251897820427/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (636602027/2500000000:ℝ) + taylorErr ≤ (251897820427/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (967753834829/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (978317372993/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (207111373879/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (251897820427/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1622951673583/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6537826117969/1000000000000:ℝ) := by nlinarith
  have hp1 : (5371965434921/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10820093095819/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2225190283313/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (545111573531/200000000000:ℝ) := by nlinarith
  have hN : (15585911379/12500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (21121585174399/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (15585911379/12500000000:ℝ) (21121585174399/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (54451693/250000000000:ℝ) ≤ ((15585911379/12500000000:ℝ)/(21121585174399/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_165 (x : ℝ) (h₁ : (529/256:ℝ) ≤ x) (h₂ : x ≤ (267/128:ℝ)) : (269688311/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2086213871/10000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (2699806187/10000000000:ℝ) := by nlinarith
  have hc1 : (38551042541/40000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (38551042541/40000000000:ℝ) ≤ taylorCos (2699806187/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (978317372993/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2086213871/10000000000:ℝ) + taylorErr ≤ (978317372993/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (207111373879/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (207111373879/1000000000000:ℝ) ≤ taylorSin (2086213871/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (33339094971/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2699806187/10000000000:ℝ) + taylorErr ≤ (33339094971/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (38551042541/40000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (978317372993/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (207111373879/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (33339094971/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1622951673583/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (819145740731/125000000000:ℝ) := by nlinarith
  have hp1 : (5371965434921/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5422740228219/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2225190283313/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (2892628023547/1000000000000:ℝ) := by nlinarith
  have hN : (15585911379/12500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (84887967303391/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (15585911379/12500000000:ℝ) (84887967303391/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (269688311/1250000000000:ℝ) ≤ ((15585911379/12500000000:ℝ)/(84887967303391/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_166 (x : ℝ) (h₁ : (529/256:ℝ) ≤ x) (h₂ : x ≤ (1073/512:ℝ)) : (264638553/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2086213871/10000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (601320469/2000000000:ℝ) := by nlinarith
  have hc1 : (477570583011/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (477570583011/500000000000:ℝ) ≤ taylorCos (601320469/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (978317372993/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2086213871/10000000000:ℝ) + taylorErr ≤ (978317372993/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (207111373879/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (207111373879/1000000000000:ℝ) ≤ taylorSin (2086213871/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (296150890577/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (601320469/2000000000:ℝ) + taylorErr ≤ (296150890577/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (477570583011/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (978317372993/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (207111373879/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (296150890577/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1622951673583/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3291922770803/500000000000:ℝ) := by nlinarith
  have hp1 : (5371965434921/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10896255177677/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2225190283313/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (403366959353/125000000000:ℝ) := by nlinarith
  have hN : (15585911379/12500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (85694044231451/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (15585911379/12500000000:ℝ) (85694044231451/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (264638553/1250000000000:ℝ) ≤ ((15585911379/12500000000:ℝ)/(85694044231451/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_167 (x : ℝ) (h₁ : (529/256:ℝ) ≤ x) (h₂ : x ≤ (539/256:ℝ)) : (259706701/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2086213871/10000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (1656699251/5000000000:ℝ) := by nlinarith
  have hc1 : (945607323113/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (945607323113/1000000000000:ℝ) ≤ taylorCos (1656699251/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (978317372993/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2086213871/10000000000:ℝ) + taylorErr ≤ (978317372993/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (207111373879/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (207111373879/1000000000000:ℝ) ≤ taylorSin (2086213871/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (8132757361/25000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1656699251/5000000000:ℝ) + taylorErr ≤ (8132757361/25000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (945607323113/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (978317372993/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (207111373879/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (8132757361/25000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1622951673583/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6614525157363/1000000000000:ℝ) := by nlinarith
  have hp1 : (5371965434921/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10947029898913/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2225190283313/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (3561181519659/1000000000000:ℝ) := by nlinarith
  have hN : (15585911379/12500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (86503886114777/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (15585911379/12500000000:ℝ) (86503886114777/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (259706701/1250000000000:ℝ) ≤ ((15585911379/12500000000:ℝ)/(86503886114777/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_168 (x : ℝ) (h₁ : (529/256:ℝ) ≤ x) (h₂ : x ≤ (17/8:ℝ)) : (2001469121/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2086213871/10000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (3926990817/10000000000:ℝ) := by nlinarith
  have hc1 : (923879530249/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (923879530249/1000000000000:ℝ) ≤ taylorCos (3926990817/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (978317372993/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2086213871/10000000000:ℝ) + taylorErr ≤ (978317372993/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (207111373879/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (207111373879/1000000000000:ℝ) ≤ taylorSin (2086213871/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (95670858657/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/10000000000:ℝ) + taylorErr ≤ (95670858657/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (923879530249/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (978317372993/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (207111373879/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (95670858657/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1622951673583/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6675884388879/1000000000000:ℝ) := by nlinarith
  have hp1 : (5371965434921/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1104857934139/100000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2225190283313/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1057027072531/250000000000:ℝ) := by nlinarith
  have hN : (15585911379/12500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (88134864747357/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (15585911379/12500000000:ℝ) (88134864747357/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2001469121/10000000000000:ℝ) ≤ ((15585911379/12500000000:ℝ)/(88134864747357/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_169 (x : ℝ) (h₁ : (2121/1024:ℝ) ≤ x) (h₂ : x ≤ (267/128:ℝ)) : (1392763463/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (44792239/200000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (2699806187/10000000000:ℝ) := by nlinarith
  have hc1 : (38551042541/40000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (38551042541/40000000000:ℝ) ≤ taylorCos (2699806187/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (121878168417/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (44792239/200000000:ℝ) + taylorErr ≤ (121878168417/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (222093618681/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (222093618681/1000000000000:ℝ) ≤ taylorSin (44792239/200000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (33339094971/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2699806187/10000000000:ℝ) + taylorErr ≤ (33339094971/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (38551042541/40000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (121878168417/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (222093618681/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (33339094971/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (650714650221/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (819145740731/125000000000:ℝ) := by nlinarith
  have hp1 : (10769318230119/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5422740228219/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1195898428227/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (2892628023547/1000000000000:ℝ) := by nlinarith
  have hN : (708385754559/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (84887967303391/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (708385754559/500000000000:ℝ) (84887967303391/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1392763463/5000000000000:ℝ) ≤ ((708385754559/500000000000:ℝ)/(84887967303391/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_170 (x : ℝ) (h₁ : (1063/512:ℝ) ≤ x) (h₂ : x ≤ (1073/512:ℝ)) : (343008739/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2393010029/10000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (601320469/2000000000:ℝ) := by nlinarith
  have hc1 : (477570583011/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (477570583011/500000000000:ℝ) ≤ taylorCos (601320469/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (971503893251/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2393010029/10000000000:ℝ) + taylorErr ≤ (971503893251/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (118511801861/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (118511801861/500000000000:ℝ) ≤ taylorSin (2393010029/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (296150890577/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (601320469/2000000000:ℝ) + taylorErr ≤ (296150890577/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (477570583011/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (971503893251/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (118511801861/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (296150890577/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6522486310089/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3291922770803/500000000000:ℝ) := by nlinarith
  have hp1 : (5397352795199/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10896255177677/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1279300010077/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (403366959353/125000000000:ℝ) := by nlinarith
  have hN : (1587096126903/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (85694044231451/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1587096126903/1000000000000:ℝ) (85694044231451/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (343008739/1000000000000:ℝ) ≤ ((1587096126903/1000000000000:ℝ)/(85694044231451/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_171 (x : ℝ) (h₁ : (1063/512:ℝ) ≤ x) (h₂ : x ≤ (539/256:ℝ)) : (3366163659/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2393010029/10000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (1656699251/5000000000:ℝ) := by nlinarith
  have hc1 : (945607323113/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (945607323113/1000000000000:ℝ) ≤ taylorCos (1656699251/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (971503893251/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2393010029/10000000000:ℝ) + taylorErr ≤ (971503893251/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (118511801861/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (118511801861/500000000000:ℝ) ≤ taylorSin (2393010029/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (8132757361/25000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1656699251/5000000000:ℝ) + taylorErr ≤ (8132757361/25000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (945607323113/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (971503893251/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (118511801861/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (8132757361/25000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6522486310089/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6614525157363/1000000000000:ℝ) := by nlinarith
  have hp1 : (5397352795199/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10947029898913/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1279300010077/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (3561181519659/1000000000000:ℝ) := by nlinarith
  have hN : (1587096126903/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (86503886114777/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1587096126903/1000000000000:ℝ) (86503886114777/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (3366163659/10000000000000:ℝ) ≤ ((1587096126903/1000000000000:ℝ)/(86503886114777/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_172 (x : ℝ) (h₁ : (267/128:ℝ) ≤ x) (h₂ : x ≤ (17/8:ℝ)) : (4789633321/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1349903093/5000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (3926990817/10000000000:ℝ) := by nlinarith
  have hc1 : (923879530249/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (923879530249/1000000000000:ℝ) ≤ taylorCos (3926990817/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (240944017019/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1349903093/5000000000:ℝ) + taylorErr ≤ (240944017019/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (266712755147/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (266712755147/1000000000000:ℝ) ≤ taylorSin (1349903093/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (95670858657/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/10000000000:ℝ) + taylorErr ≤ (95670858657/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (923879530249/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (240944017019/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (266712755147/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (95670858657/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6553165925847/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6675884388879/1000000000000:ℝ) := by nlinarith
  have hp1 : (2169096062191/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1104857934139/100000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2892627934627/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1057027072531/250000000000:ℝ) := by nlinarith
  have hN : (1928851866551/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (88134864747357/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1928851866551/1000000000000:ℝ) (88134864747357/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (4789633321/10000000000000:ℝ) ≤ ((1928851866551/1000000000000:ℝ)/(88134864747357/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_173 (x : ℝ) (h₁ : (267/128:ℝ) ≤ x) (h₂ : x ≤ (549/256:ℝ)) : (4615617497/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1349903093/5000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (4540583133/10000000000:ℝ) := by nlinarith
  have hc1 : (449337231697/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (449337231697/500000000000:ℝ) ≤ taylorCos (4540583133/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (240944017019/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1349903093/5000000000:ℝ) + taylorErr ≤ (240944017019/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (266712755147/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (266712755147/1000000000000:ℝ) ≤ taylorSin (1349903093/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (219308120439/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (4540583133/10000000000:ℝ) + taylorErr ≤ (219308120439/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (449337231697/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (240944017019/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (266712755147/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (219308120439/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6553165925847/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3368621810197/500000000000:ℝ) := by nlinarith
  have hp1 : (2169096062191/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5575064391933/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2892627934627/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (978125514497/200000000000:ℝ) := by nlinarith
  have hN : (1928851866551/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (2244522580027/25000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1928851866551/1000000000000:ℝ) (2244522580027/25000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (4615617497/10000000000000:ℝ) ≤ ((1928851866551/1000000000000:ℝ)/(2244522580027/25000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_174 (x : ℝ) (h₁ : (267/128:ℝ) ≤ x) (h₂ : x ≤ (277/128:ℝ)) : (1112362433/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1349903093/5000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (644271931/1250000000:ℝ) := by nlinarith
  have hc1 : (870086988811/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (870086988811/1000000000000:ℝ) ≤ taylorCos (644271931/1250000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (240944017019/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1349903093/5000000000:ℝ) + taylorErr ≤ (240944017019/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (266712755147/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (266712755147/1000000000000:ℝ) ≤ taylorSin (1349903093/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (492898194553/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (644271931/1250000000:ℝ) + taylorErr ≤ (492898194553/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (870086988811/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (240944017019/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (266712755147/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (492898194553/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6553165925847/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (679860285191/100000000000:ℝ) := by nlinarith
  have hp1 : (2169096062191/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (11251678226343/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2892627934627/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (86655185679/15625000000:ℝ) := by nlinarith
  have hN : (1928851866551/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (45721000737999/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1928851866551/1000000000000:ℝ) (45721000737999/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1112362433/2500000000000:ℝ) ≤ ((1928851866551/1000000000000:ℝ)/(45721000737999/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_175 (x : ℝ) (h₁ : (267/128:ℝ) ≤ x) (h₂ : x ≤ (141/64:ℝ)) : (129343671/312500000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1349903093/5000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (3190680039/5000000000:ℝ) := by nlinarith
  have hc1 : (160641505837/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (160641505837/200000000000:ℝ) ≤ taylorCos (3190680039/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (240944017019/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1349903093/5000000000:ℝ) + taylorErr ≤ (240944017019/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (266712755147/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (266712755147/1000000000000:ℝ) ≤ taylorSin (1349903093/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (297849653393/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3190680039/5000000000:ℝ) + taylorErr ≤ (297849653393/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (160641505837/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (240944017019/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (266712755147/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (297849653393/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6553165925847/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6921321314941/1000000000000:ℝ) := by nlinarith
  have hp1 : (2169096062191/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2290955422259/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2892627934627/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (6823602784587/1000000000000:ℝ) := by nlinarith
  have hN : (1928851866551/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (47404688744657/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1928851866551/1000000000000:ℝ) (47404688744657/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (129343671/312500000000:ℝ) ≤ ((1928851866551/1000000000000:ℝ)/(47404688744657/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_176 (x : ℝ) (h₁ : (539/256:ℝ) ≤ x) (h₂ : x ≤ (549/256:ℝ)) : (4243616393/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (3313398501/10000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (4540583133/10000000000:ℝ) := by nlinarith
  have hc1 : (449337231697/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (449337231697/500000000000:ℝ) ≤ taylorCos (4540583133/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (94560732767/100000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (3313398501/10000000000:ℝ) + taylorErr ≤ (94560732767/100000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (325310289821/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (325310289821/1000000000000:ℝ) ≤ taylorSin (3313398501/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (219308120439/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (4540583133/10000000000:ℝ) + taylorErr ≤ (219308120439/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (449337231697/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (94560732767/100000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (325310289821/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (219308120439/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3307262578681/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3368621810197/500000000000:ℝ) := by nlinarith
  have hp1 : (2736757438017/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5575064391933/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (890295355331/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (978125514497/200000000000:ℝ) := by nlinarith
  have hN : (1307787046827/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (2244522580027/25000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1307787046827/500000000000:ℝ) (2244522580027/25000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (4243616393/5000000000000:ℝ) ≤ ((1307787046827/500000000000:ℝ)/(2244522580027/25000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_177 (x : ℝ) (h₁ : (539/256:ℝ) ≤ x) (h₂ : x ≤ (277/128:ℝ)) : (2045420557/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (3313398501/10000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (644271931/1250000000:ℝ) := by nlinarith
  have hc1 : (870086988811/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (870086988811/1000000000000:ℝ) ≤ taylorCos (644271931/1250000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (94560732767/100000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (3313398501/10000000000:ℝ) + taylorErr ≤ (94560732767/100000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (325310289821/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (325310289821/1000000000000:ℝ) ≤ taylorSin (3313398501/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (492898194553/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (644271931/1250000000:ℝ) + taylorErr ≤ (492898194553/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (870086988811/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (94560732767/100000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (325310289821/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (492898194553/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3307262578681/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (679860285191/100000000000:ℝ) := by nlinarith
  have hp1 : (2736757438017/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (11251678226343/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (890295355331/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (86655185679/15625000000:ℝ) := by nlinarith
  have hN : (1307787046827/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (45721000737999/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1307787046827/500000000000:ℝ) (45721000737999/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2045420557/2500000000000:ℝ) ≤ ((1307787046827/500000000000:ℝ)/(45721000737999/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_178 (x : ℝ) (h₁ : (17/8:ℝ) ≤ x) (h₂ : x ≤ (141/64:ℝ)) : (48584483/40000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/312500000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (3190680039/5000000000:ℝ) := by nlinarith
  have hc1 : (160641505837/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (160641505837/200000000000:ℝ) ≤ taylorCos (3190680039/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (923879534811/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/312500000:ℝ) + taylorErr ≤ (923879534811/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (95670857503/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (95670857503/250000000000:ℝ) ≤ taylorSin (122718463/312500000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (297849653393/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3190680039/5000000000:ℝ) + taylorErr ≤ (297849653393/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (160641505837/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (923879534811/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (95670857503/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (297849653393/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3337942194439/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6921321314941/1000000000000:ℝ) := by nlinarith
  have hp1 : (11048579193183/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2290955422259/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2114054091203/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (6823602784587/1000000000000:ℝ) := by nlinarith
  have hN : (660845729519/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (47404688744657/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (660845729519/200000000000:ℝ) (47404688744657/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (48584483/40000000000:ℝ) ≤ ((660845729519/200000000000:ℝ)/(47404688744657/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_179 (x : ℝ) (h₁ : (17/8:ℝ) ≤ x) (h₂ : x ≤ (9/4:ℝ)) : (2788858101/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/312500000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (923879534811/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/312500000:ℝ) + taylorErr ≤ (923879534811/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (95670857503/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (95670857503/250000000000:ℝ) ≤ taylorSin (122718463/312500000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (176776695861/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/5000000000:ℝ) + taylorErr ≤ (176776695861/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (923879534811/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (95670857503/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (176776695861/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3337942194439/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3534291735289/500000000000:ℝ) := by nlinarith
  have hp1 : (11048579193183/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (11698495773237/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2114054091203/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (8272085717347/1000000000000:ℝ) := by nlinarith
  have hN : (660845729519/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (49464872280529/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (660845729519/200000000000:ℝ) (49464872280529/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2788858101/2500000000000:ℝ) ≤ ((660845729519/200000000000:ℝ)/(49464872280529/500000000000:ℝ))^2 := by norm_num
  linarith

end Zeta23Ext.Bridge.FourPoint
