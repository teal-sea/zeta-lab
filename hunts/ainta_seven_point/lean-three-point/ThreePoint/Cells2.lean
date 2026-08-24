import ThreePoint.Base

noncomputable section
open Real
namespace Zeta23Ext.Bridge.ThreePoint


theorem wc_120 (x : ℝ) (h₁ : (8203/4096:ℝ) ≤ x) (h₂ : x ≤ (4103/2048:ℝ)) : (10069211/78125000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (84368943/10000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (3355583/312500000:ℝ) := by nlinarith
  have hc1 : (999942347413/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (999942347413/1000000000000:ℝ) ≤ taylorCos (3355583/312500000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (999964411881/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (84368943/10000000000:ℝ) + taylorErr ≤ (999964411881/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (8436791947/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (8436791947/1000000000000:ℝ) ≤ taylorSin (84368943/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (5368830757/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3355583/312500000:ℝ) + taylorErr ≤ (5368830757/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (999942347413/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999964411881/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (8436791947/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (5368830757/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (786452775189/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1258784634539/200000000000:ℝ) := by nlinarith
  have hp1 : (10412625818207/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1302054257747/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1756983153/20000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (111848143141/1000000000000:ℝ) := by nlinarith
  have hN : (55505887767/62500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (3129077512303/40000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (55505887767/62500000000:ℝ) (3129077512303/40000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (10069211/78125000000:ℝ) ≤ ((55505887767/62500000000:ℝ)/(3129077512303/40000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_121 (x : ℝ) (h₁ : (16409/8192:ℝ) ≤ x) (h₂ : x ≤ (4103/2048:ℝ)) : (10069211/78125000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (95873799/10000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (3355583/312500000:ℝ) := by nlinarith
  have hc1 : (999942347413/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (999942347413/1000000000000:ℝ) ≤ taylorCos (3355583/312500000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (124994255461/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (95873799/10000000000:ℝ) + taylorErr ≤ (124994255461/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (9587230763/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (9587230763/1000000000000:ℝ) ≤ taylorSin (95873799/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (5368830757/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3355583/312500000:ℝ) + taylorErr ≤ (5368830757/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (999942347413/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (124994255461/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (9587230763/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (5368830757/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6292772687103/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1258784634539/200000000000:ℝ) := by nlinarith
  have hp1 : (2603632467557/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1302054257747/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (49923250577/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (111848143141/1000000000000:ℝ) := by nlinarith
  have hN : (55505887767/62500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (3129077512303/40000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (55505887767/62500000000:ℝ) (3129077512303/40000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (10069211/78125000000:ℝ) ≤ ((55505887767/62500000000:ℝ)/(3129077512303/40000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_122 (x : ℝ) (h₁ : (4103/2048:ℝ) ≤ x) (h₂ : x ≤ (16415/8192:ℝ)) : (1253281709/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (21475731/2000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (14860439/1250000000:ℝ) := by nlinarith
  have hc1 : (999929332123/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (999929332123/1000000000000:ℝ) ≤ taylorCos (14860439/1250000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (499971175969/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (21475731/2000000000:ℝ) + taylorErr ≤ (499971175969/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (1073765689/100000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (1073765689/100000000000:ℝ) ≤ taylorSin (21475731/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (2972018357/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (14860439/1250000000:ℝ) + taylorErr ≤ (2972018357/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (999929332123/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (499971175969/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (1073765689/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (2972018357/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3146961586347/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3147536829143/500000000000:ℝ) := by nlinarith
  have hp1 : (10416433922249/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10418338114023/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (55924046737/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (61926984249/500000000000:ℝ) := by nlinarith
  have hN : (7008602909/8000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (78255904726493/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (7008602909/8000000000:ℝ) (78255904726493/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1253281709/10000000000000:ℝ) ≤ ((7008602909/8000000000:ℝ)/(78255904726493/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_123 (x : ℝ) (h₁ : (4103/2048:ℝ) ≤ x) (h₂ : x ≤ (8209/4096:ℝ)) : (1218212331/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (21475731/2000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (130388367/10000000000:ℝ) := by nlinarith
  have hc1 : (999914993311/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (999914993311/1000000000000:ℝ) ≤ taylorCos (130388367/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (499971175969/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (21475731/2000000000:ℝ) + taylorErr ≤ (499971175969/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (1073765689/100000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (1073765689/100000000000:ℝ) ≤ taylorSin (21475731/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (13038469507/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (130388367/10000000000:ℝ) + taylorErr ≤ (13038469507/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (999914993311/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (499971175969/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (1073765689/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (13038469507/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3146961586347/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6296224143877/1000000000000:ℝ) := by nlinarith
  have hp1 : (10416433922249/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1042024216607/100000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (55924046737/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (67932004869/500000000000:ℝ) := by nlinarith
  have hN : (864050983573/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (1957121923497/25000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (864050983573/1000000000000:ℝ) (1957121923497/25000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1218212331/10000000000000:ℝ) ≤ ((864050983573/1000000000000:ℝ)/(1957121923497/25000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_124 (x : ℝ) (h₁ : (4103/2048:ℝ) ≤ x) (h₂ : x ≤ (2053/1024:ℝ)) : (143699471/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (21475731/2000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (153398079/10000000000:ℝ) := by nlinarith
  have hc1 : (124985293149/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (124985293149/125000000000:ℝ) ≤ taylorCos (153398079/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (499971175969/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (21475731/2000000000:ℝ) + taylorErr ≤ (499971175969/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (1073765689/100000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (1073765689/100000000000:ℝ) ≤ taylorSin (21475731/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (1917401071/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (153398079/10000000000:ℝ) + taylorErr ≤ (1917401071/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (124985293149/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (499971175969/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (1073765689/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1917401071/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3146961586347/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6298525115059/1000000000000:ℝ) := by nlinarith
  have hp1 : (10416433922249/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10424050270163/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (55924046737/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (79948340609/500000000000:ℝ) := by nlinarith
  have hN : (419992831987/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (39171418625029/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (419992831987/500000000000:ℝ) (39171418625029/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (143699471/1250000000000:ℝ) ≤ ((419992831987/500000000000:ℝ)/(39171418625029/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_125 (x : ℝ) (h₁ : (16415/8192:ℝ) ≤ x) (h₂ : x ≤ (8209/4096:ℝ)) : (1218212331/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (118883511/10000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (130388367/10000000000:ℝ) := by nlinarith
  have hc1 : (999914993311/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (999914993311/1000000000000:ℝ) ≤ taylorCos (130388367/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (124991167081/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (118883511/10000000000:ℝ) + taylorErr ≤ (124991167081/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (2972017201/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (2972017201/250000000000:ℝ) ≤ taylorSin (118883511/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (13038469507/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (130388367/10000000000:ℝ) + taylorErr ≤ (13038469507/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (999914993311/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (124991167081/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (2972017201/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (13038469507/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1259014731657/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6296224143877/1000000000000:ℝ) := by nlinarith
  have hp1 : (1041833797427/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1042024216607/100000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (123853918661/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (67932004869/500000000000:ℝ) := by nlinarith
  have hN : (864050983573/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (1957121923497/25000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (864050983573/1000000000000:ℝ) (1957121923497/25000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1218212331/10000000000000:ℝ) ≤ ((864050983573/1000000000000:ℝ)/(1957121923497/25000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_126 (x : ℝ) (h₁ : (8209/4096:ℝ) ≤ x) (h₂ : x ≤ (16421/8192:ℝ)) : (1183650479/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (65194183/5000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (141893223/10000000000:ℝ) := by nlinarith
  have hc1 : (999899330993/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (999899330993/1000000000000:ℝ) ≤ taylorCos (141893223/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (999914997837/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (65194183/5000000000:ℝ) + taylorErr ≤ (999914997837/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (13038464883/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (13038464883/1000000000000:ℝ) ≤ taylorSin (65194183/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (3547212107/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (141893223/10000000000:ℝ) + taylorErr ≤ (3547212107/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (999899330993/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999914997837/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (13038464883/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (3547212107/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1574056035969/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1574343657367/250000000000:ℝ) := by nlinarith
  have hp1 : (10420242026291/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2605536554529/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (33965989933/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (18484781623/125000000000:ℝ) := by nlinarith
  have hN : (852021078009/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (15662770889547/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (852021078009/1000000000000:ℝ) (15662770889547/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1183650479/10000000000000:ℝ) ≤ ((852021078009/1000000000000:ℝ)/(15662770889547/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_127 (x : ℝ) (h₁ : (8209/4096:ℝ) ≤ x) (h₂ : x ≤ (2053/1024:ℝ)) : (143699471/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (65194183/5000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (153398079/10000000000:ℝ) := by nlinarith
  have hc1 : (124985293149/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (124985293149/125000000000:ℝ) ≤ taylorCos (153398079/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (999914997837/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (65194183/5000000000:ℝ) + taylorErr ≤ (999914997837/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (13038464883/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (13038464883/1000000000000:ℝ) ≤ taylorSin (65194183/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (1917401071/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (153398079/10000000000:ℝ) + taylorErr ≤ (1917401071/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (124985293149/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999914997837/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (13038464883/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1917401071/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1574056035969/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6298525115059/1000000000000:ℝ) := by nlinarith
  have hp1 : (10420242026291/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10424050270163/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (33965989933/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (79948340609/500000000000:ℝ) := by nlinarith
  have hN : (419992831987/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (39171418625029/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (419992831987/500000000000:ℝ) (39171418625029/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (143699471/1250000000000:ℝ) ≤ ((419992831987/500000000000:ℝ)/(39171418625029/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_128 (x : ℝ) (h₁ : (16421/8192:ℝ) ≤ x) (h₂ : x ≤ (2053/1024:ℝ)) : (143699471/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (70946611/5000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (153398079/10000000000:ℝ) := by nlinarith
  have hc1 : (124985293149/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (124985293149/125000000000:ℝ) ≤ taylorCos (153398079/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (999899335519/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (70946611/5000000000:ℝ) + taylorErr ≤ (999899335519/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (3547210951/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (3547210951/250000000000:ℝ) ≤ taylorSin (70946611/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (1917401071/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (153398079/10000000000:ℝ) + taylorErr ≤ (1917401071/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (124985293149/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999899335519/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (3547210951/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1917401071/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6297374629467/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6298525115059/1000000000000:ℝ) := by nlinarith
  have hp1 : (1302768259789/125000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10424050270163/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (147878202807/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (79948340609/500000000000:ℝ) := by nlinarith
  have hN : (419992831987/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (39171418625029/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (419992831987/500000000000:ℝ) (39171418625029/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (143699471/1250000000000:ℝ) ≤ ((419992831987/500000000000:ℝ)/(39171418625029/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_129 (x : ℝ) (h₁ : (2053/1024:ℝ) ≤ x) (h₂ : x ≤ (16427/8192:ℝ)) : (1116047803/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (76699039/5000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (32980587/2000000000:ℝ) := by nlinarith
  have hc1 : (999864035929/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (999864035929/1000000000000:ℝ) ≤ taylorCos (32980587/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (499941174859/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (76699039/5000000000:ℝ) + taylorErr ≤ (499941174859/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (1917400493/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (1917400493/125000000000:ℝ) ≤ taylorSin (76699039/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (3297909681/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (32980587/2000000000:ℝ) + taylorErr ≤ (3297909681/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (999864035929/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (499941174859/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (1917400493/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (3297909681/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3149262557529/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (125993512013/20000000000:ℝ) := by nlinarith
  have hp1 : (10424050130333/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10425954322209/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (159896630871/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (34383855693/200000000000:ℝ) := by nlinarith
  have hN : (103493094683/125000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (1567436506937/20000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (103493094683/125000000000:ℝ) (1567436506937/20000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1116047803/10000000000000:ℝ) ≤ ((103493094683/125000000000:ℝ)/(1567436506937/20000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_130 (x : ℝ) (h₁ : (2053/1024:ℝ) ≤ x) (h₂ : x ≤ (8215/4096:ℝ)) : (67687887/625000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (76699039/5000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (176407791/10000000000:ℝ) := by nlinarith
  have hc1 : (999844403229/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (999844403229/1000000000000:ℝ) ≤ taylorCos (176407791/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (499941174859/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (76699039/5000000000:ℝ) + taylorErr ≤ (499941174859/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (1917400493/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (1917400493/125000000000:ℝ) ≤ taylorSin (76699039/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (17639866417/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (176407791/10000000000:ℝ) + taylorErr ≤ (17639866417/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (999844403229/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (499941174859/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (1917400493/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (17639866417/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3149262557529/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6300826086241/1000000000000:ℝ) := by nlinarith
  have hp1 : (10424050130333/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (651741148391/62500000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (159896630871/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (91973014369/500000000000:ℝ) := by nlinarith
  have hN : (815898374491/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (78400818738111/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (815898374491/1000000000000:ℝ) (78400818738111/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (67687887/625000000000:ℝ) ≤ ((815898374491/1000000000000:ℝ)/(78400818738111/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_131 (x : ℝ) (h₁ : (2053/1024:ℝ) ≤ x) (h₂ : x ≤ (4109/2048:ℝ)) : (509220219/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (76699039/5000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (199417503/10000000000:ℝ) := by nlinarith
  have hc1 : (7998409341/8000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (7998409341/8000000000:ℝ) ≤ taylorCos (199417503/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (499941174859/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (76699039/5000000000:ℝ) + taylorErr ≤ (499941174859/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (1917400493/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (1917400493/125000000000:ℝ) ≤ taylorSin (76699039/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (19940430871/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (199417503/10000000000:ℝ) + taylorErr ≤ (19940430871/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (7998409341/8000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (499941174859/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (1917400493/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (19940430871/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3149262557529/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6303127057423/1000000000000:ℝ) := by nlinarith
  have hp1 : (10424050130333/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10431666478349/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (159896630871/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (208011924281/1000000000000:ℝ) := by nlinarith
  have hN : (49486827709/62500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (19614705351009/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (49486827709/62500000000:ℝ) (19614705351009/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (509220219/5000000000000:ℝ) ≤ ((49486827709/62500000000:ℝ)/(19614705351009/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_132 (x : ℝ) (h₁ : (2053/1024:ℝ) ≤ x) (h₂ : x ≤ (257/128:ℝ)) : (179073511/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (76699039/5000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (245436927/10000000000:ℝ) := by nlinarith
  have hc1 : (62481176027/62500000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (62481176027/62500000000:ℝ) ≤ taylorCos (245436927/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (499941174859/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (76699039/5000000000:ℝ) + taylorErr ≤ (499941174859/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (1917400493/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (1917400493/125000000000:ℝ) ≤ taylorSin (76699039/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (499941174859/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (1917400493/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (24541230879/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3149262557529/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3153864499893/500000000000:ℝ) := by nlinarith
  have hp1 : (10424050130333/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5219641343267/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (159896630871/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (128096423311/500000000000:ℝ) := by nlinarith
  have hN : (74350596981/100000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (78574890269483/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (74350596981/100000000000:ℝ) (78574890269483/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (179073511/2000000000000:ℝ) ≤ ((74350596981/100000000000:ℝ)/(78574890269483/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_133 (x : ℝ) (h₁ : (16427/8192:ℝ) ≤ x) (h₂ : x ≤ (8215/4096:ℝ)) : (67687887/625000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (82451467/5000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (176407791/10000000000:ℝ) := by nlinarith
  have hc1 : (999844403229/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (999844403229/1000000000000:ℝ) ≤ taylorCos (176407791/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (199972808091/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (82451467/5000000000:ℝ) + taylorErr ≤ (199972808091/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (16489543781/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (16489543781/1000000000000:ℝ) ≤ taylorSin (82451467/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (17639866417/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (176407791/10000000000:ℝ) + taylorErr ≤ (17639866417/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (999844403229/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (199972808091/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (16489543781/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (17639866417/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6299675600649/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6300826086241/1000000000000:ℝ) := by nlinarith
  have hp1 : (5212977091177/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (651741148391/62500000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (42979806987/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (91973014369/500000000000:ℝ) := by nlinarith
  have hN : (815898374491/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (78400818738111/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (815898374491/1000000000000:ℝ) (78400818738111/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (67687887/625000000000:ℝ) ≤ ((815898374491/1000000000000:ℝ)/(78400818738111/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_134 (x : ℝ) (h₁ : (8215/4096:ℝ) ≤ x) (h₂ : x ≤ (4109/2048:ℝ)) : (509220219/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (17640779/1000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (199417503/10000000000:ℝ) := by nlinarith
  have hc1 : (7998409341/8000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (7998409341/8000000000:ℝ) ≤ taylorCos (199417503/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (199968881551/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (17640779/1000000000:ℝ) + taylorErr ≤ (199968881551/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (551245681/31250000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (551245681/31250000000:ℝ) ≤ taylorSin (17640779/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (19940430871/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (199417503/10000000000:ℝ) + taylorErr ≤ (19940430871/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (7998409341/8000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (199968881551/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (551245681/31250000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (19940430871/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (39380163039/6250000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6303127057423/1000000000000:ℝ) := by nlinarith
  have hp1 : (667382927/64000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10431666478349/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4598649451/25000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (208011924281/1000000000000:ℝ) := by nlinarith
  have hN : (49486827709/62500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (19614705351009/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (49486827709/62500000000:ℝ) (19614705351009/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (509220219/5000000000000:ℝ) ≤ ((49486827709/62500000000:ℝ)/(19614705351009/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_135 (x : ℝ) (h₁ : (4109/2048:ℝ) ≤ x) (h₂ : x ≤ (8221/4096:ℝ)) : (119486913/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (99708751/5000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (44485443/2000000000:ℝ) := by nlinarith
  have hc1 : (499876319303/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (499876319303/500000000000:ℝ) ≤ taylorCos (44485443/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (999801172151/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (99708751/5000000000:ℝ) + taylorErr ≤ (999801172151/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (19940426247/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (19940426247/1000000000000:ℝ) ≤ taylorSin (99708751/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (2780111219/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (44485443/2000000000:ℝ) + taylorErr ≤ (2780111219/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (499876319303/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999801172151/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (19940426247/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (2780111219/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3151563528711/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1576357007151/250000000000:ℝ) := by nlinarith
  have hp1 : (10431666338417/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (260886864561/25000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (104005936627/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (116047119849/500000000000:ℝ) := by nlinarith
  have hN : (191914599727/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (7851684524781/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (191914599727/250000000000:ℝ) (7851684524781/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (119486913/1250000000000:ℝ) ≤ ((191914599727/250000000000:ℝ)/(7851684524781/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_136 (x : ℝ) (h₁ : (4109/2048:ℝ) ≤ x) (h₂ : x ≤ (257/128:ℝ)) : (179073511/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (99708751/5000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (245436927/10000000000:ℝ) := by nlinarith
  have hc1 : (62481176027/62500000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (62481176027/62500000000:ℝ) ≤ taylorCos (245436927/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (999801172151/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (99708751/5000000000:ℝ) + taylorErr ≤ (999801172151/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (19940426247/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (19940426247/1000000000000:ℝ) ≤ taylorSin (99708751/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (999801172151/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (19940426247/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (24541230879/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3151563528711/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3153864499893/500000000000:ℝ) := by nlinarith
  have hp1 : (10431666338417/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5219641343267/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (104005936627/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (128096423311/500000000000:ℝ) := by nlinarith
  have hN : (74350596981/100000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (78574890269483/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (74350596981/100000000000:ℝ) (78574890269483/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (179073511/2000000000000:ℝ) ≤ ((74350596981/100000000000:ℝ)/(78574890269483/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_137 (x : ℝ) (h₁ : (8221/4096:ℝ) ≤ x) (h₂ : x ≤ (257/128:ℝ)) : (179073511/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (111213607/5000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (245436927/10000000000:ℝ) := by nlinarith
  have hc1 : (62481176027/62500000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (62481176027/62500000000:ℝ) ≤ taylorCos (245436927/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (999752643133/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (111213607/5000000000:ℝ) + taylorErr ≤ (999752643133/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (2780110641/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (2780110641/125000000000:ℝ) ≤ taylorSin (111213607/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (999752643133/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (2780110641/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (24541230879/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6305428028603/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3153864499893/500000000000:ℝ) := by nlinarith
  have hp1 : (10435474442457/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5219641343267/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (23209418833/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (128096423311/500000000000:ℝ) := by nlinarith
  have hN : (74350596981/100000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (78574890269483/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (74350596981/100000000000:ℝ) (78574890269483/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (179073511/2000000000000:ℝ) ≤ ((74350596981/100000000000:ℝ)/(78574890269483/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_138 (x : ℝ) (h₁ : (257/128:ℝ) ≤ x) (h₂ : x ≤ (8227/4096:ℝ)) : (836853921/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/5000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (134223319/5000000000:ℝ) := by nlinarith
  have hc1 : (249909925347/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (249909925347/250000000000:ℝ) ≤ taylorCos (134223319/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (999698820959/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/5000000000:ℝ) + taylorErr ≤ (999698820959/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (4908245251/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (4908245251/200000000000:ℝ) ≤ taylorSin (122718463/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (26841441973/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (134223319/5000000000:ℝ) + taylorErr ≤ (26841441973/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (249909925347/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999698820959/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (4908245251/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (26841441973/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1261545799957/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (788753746371/125000000000:ℝ) := by nlinarith
  have hp1 : (10439282546499/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10443090790627/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (256192794913/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (70076903869/250000000000:ℝ) := by nlinarith
  have hN : (89916510739/125000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (78632956469029/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (89916510739/125000000000:ℝ) (78632956469029/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (836853921/10000000000000:ℝ) ≤ ((89916510739/125000000000:ℝ)/(78632956469029/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_139 (x : ℝ) (h₁ : (257/128:ℝ) ≤ x) (h₂ : x ≤ (4115/2048:ℝ)) : (48771943/625000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/5000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (5829127/200000000:ℝ) := by nlinarith
  have hc1 : (124946911723/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (124946911723/125000000000:ℝ) ≤ taylorCos (5829127/200000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (999698820959/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/5000000000:ℝ) + taylorErr ≤ (999698820959/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (4908245251/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (4908245251/200000000000:ℝ) ≤ taylorSin (122718463/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (29141511057/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (5829127/200000000:ℝ) + taylorErr ≤ (29141511057/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (124946911723/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999698820959/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (4908245251/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (29141511057/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1261545799957/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (126246618843/20000000000:ℝ) := by nlinarith
  have hp1 : (10439282546499/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (16323279523/1562500000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (256192794913/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (76109604913/250000000000:ℝ) := by nlinarith
  have hN : (173784218533/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (78691043846449/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (173784218533/250000000000:ℝ) (78691043846449/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (48771943/625000000000:ℝ) ≤ ((173784218533/250000000000:ℝ)/(78691043846449/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_140 (x : ℝ) (h₁ : (257/128:ℝ) ≤ x) (h₂ : x ≤ (2059/1024:ℝ)) : (67336443/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/5000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (168737887/5000000000:ℝ) := by nlinarith
  have hc1 : (999430602291/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (999430602291/1000000000000:ℝ) ≤ taylorCos (168737887/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (999698820959/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/5000000000:ℝ) + taylorErr ≤ (999698820959/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (4908245251/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (4908245251/200000000000:ℝ) ≤ taylorSin (122718463/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (1687058709/50000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (168737887/5000000000:ℝ) + taylorErr ≤ (1687058709/50000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (999430602291/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999698820959/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (4908245251/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1687058709/50000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1261545799957/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3158466442257/500000000000:ℝ) := by nlinarith
  have hp1 : (10439282546499/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5227257551453/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (256192794913/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (70549523011/200000000000:ℝ) := by nlinarith
  have hN : (161670746809/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (78807282134909/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (161670746809/250000000000:ℝ) (78807282134909/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (67336443/1000000000000:ℝ) ≤ ((161670746809/250000000000:ℝ)/(78807282134909/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_141 (x : ℝ) (h₁ : (257/128:ℝ) ≤ x) (h₂ : x ≤ (1031/512:ℝ)) : (60421417/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/5000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (429514621/10000000000:ℝ) := by nlinarith
  have hc1 : (999077725489/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (999077725489/1000000000000:ℝ) ≤ taylorCos (429514621/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (999698820959/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/5000000000:ℝ) + taylorErr ≤ (999698820959/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (4908245251/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (4908245251/200000000000:ℝ) ≤ taylorSin (122718463/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (10734564809/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (429514621/10000000000:ℝ) + taylorErr ≤ (10734564809/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (999077725489/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999698820959/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (4908245251/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (10734564809/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1261545799957/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6326136769241/1000000000000:ℝ) := by nlinarith
  have hp1 : (10439282546499/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10469747519277/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (256192794913/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (449552733119/1000000000000:ℝ) := by nlinarith
  have hN : (54952499237/100000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (39520006423143/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (54952499237/100000000000:ℝ) (39520006423143/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (60421417/1250000000000:ℝ) ≤ ((54952499237/100000000000:ℝ)/(39520006423143/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_142 (x : ℝ) (h₁ : (257/128:ℝ) ≤ x) (h₂ : x ≤ (517/256:ℝ)) : (99255251/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/5000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (153398079/2500000000:ℝ) := by nlinarith
  have hc1 : (998118110633/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (998118110633/1000000000000:ℝ) ≤ taylorCos (153398079/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (999698820959/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/5000000000:ℝ) + taylorErr ≤ (999698820959/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (4908245251/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (4908245251/200000000000:ℝ) ≤ taylorSin (122718463/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (61320738649/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (153398079/2500000000:ℝ) + taylorErr ≤ (61320738649/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (998118110633/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999698820959/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (4908245251/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (61320738649/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1261545799957/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (793068067337/125000000000:ℝ) := by nlinarith
  have hp1 : (10439282546499/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (525010617601/50000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (256192794913/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (321940388699/500000000000:ℝ) := by nlinarith
  have hN : (70847466647/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (15901298161399/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (70847466647/200000000000:ℝ) (15901298161399/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (99255251/5000000000000:ℝ) ≤ ((70847466647/200000000000:ℝ)/(15901298161399/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_143 (x : ℝ) (_h₁ : (257/128:ℝ) ≤ x) (_h₂ : x ≤ (65/32:ℝ)) : (0:ℝ) ≤ wfun x := wfun_nonneg x

theorem wc_144 (x : ℝ) (h₁ : (8227/4096:ℝ) ≤ x) (h₂ : x ≤ (4115/2048:ℝ)) : (48771943/625000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (268446637/10000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (5829127/200000000:ℝ) := by nlinarith
  have hc1 : (124946911723/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (124946911723/125000000000:ℝ) ≤ taylorCos (5829127/200000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (199927941183/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (268446637/10000000000:ℝ) + taylorErr ≤ (199927941183/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (26841437349/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (26841437349/1000000000000:ℝ) ≤ taylorSin (268446637/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (29141511057/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (5829127/200000000:ℝ) + taylorErr ≤ (29141511057/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (124946911723/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (199927941183/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (26841437349/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (29141511057/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6310029970967/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (126246618843/20000000000:ℝ) := by nlinarith
  have hp1 : (10443090650541/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (16323279523/1562500000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (140153781713/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (76109604913/250000000000:ℝ) := by nlinarith
  have hN : (173784218533/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (78691043846449/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (173784218533/250000000000:ℝ) (78691043846449/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (48771943/625000000000:ℝ) ≤ ((173784218533/250000000000:ℝ)/(78691043846449/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_145 (x : ℝ) (h₁ : (4115/2048:ℝ) ≤ x) (h₂ : x ≤ (2059/1024:ℝ)) : (67336443/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (291456349/10000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (168737887/5000000000:ℝ) := by nlinarith
  have hc1 : (999430602291/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (999430602291/1000000000000:ℝ) ≤ taylorCos (168737887/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (999575298311/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (291456349/10000000000:ℝ) + taylorErr ≤ (999575298311/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (227668019/7812500000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (227668019/7812500000:ℝ) ≤ taylorSin (291456349/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (1687058709/50000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (168737887/5000000000:ℝ) + taylorErr ≤ (1687058709/50000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (999430602291/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999575298311/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (227668019/7812500000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1687058709/50000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6312330942149/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3158466442257/500000000000:ℝ) := by nlinarith
  have hp1 : (10446898754583/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5227257551453/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (304438367251/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (70549523011/200000000000:ℝ) := by nlinarith
  have hN : (161670746809/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (78807282134909/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (161670746809/250000000000:ℝ) (78807282134909/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (67336443/1000000000000:ℝ) ≤ ((161670746809/250000000000:ℝ)/(78807282134909/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_146 (x : ℝ) (h₁ : (2059/1024:ℝ) ≤ x) (h₂ : x ≤ (4121/2048:ℝ)) : (574380421/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (337475773/10000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (383495197/10000000000:ℝ) := by nlinarith
  have hc1 : (15613511641/15625000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (15613511641/15625000000:ℝ) ≤ taylorCos (383495197/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (999430606819/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (337475773/10000000000:ℝ) + taylorErr ≤ (999430606819/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (8435292389/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (8435292389/250000000000:ℝ) ≤ taylorSin (337475773/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (38340122639/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (383495197/10000000000:ℝ) + taylorErr ≤ (38340122639/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (15613511641/15625000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999430606819/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (8435292389/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (38340122639/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6316932884513/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6321534826877/1000000000000:ℝ) := by nlinarith
  have hp1 : (2613628740667/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10462131311091/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (352747561981/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (401119397533/1000000000000:ℝ) := by nlinarith
  have hN : (598145347491/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (39461802567419/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (598145347491/1000000000000:ℝ) (39461802567419/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (574380421/10000000000000:ℝ) ≤ ((598145347491/1000000000000:ℝ)/(39461802567419/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_147 (x : ℝ) (h₁ : (2059/1024:ℝ) ≤ x) (h₂ : x ≤ (1031/512:ℝ)) : (60421417/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (337475773/10000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (429514621/10000000000:ℝ) := by nlinarith
  have hc1 : (999077725489/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (999077725489/1000000000000:ℝ) ≤ taylorCos (429514621/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (999430606819/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (337475773/10000000000:ℝ) + taylorErr ≤ (999430606819/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (8435292389/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (8435292389/250000000000:ℝ) ≤ taylorSin (337475773/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (10734564809/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (429514621/10000000000:ℝ) + taylorErr ≤ (10734564809/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (999077725489/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999430606819/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (8435292389/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (10734564809/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6316932884513/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6326136769241/1000000000000:ℝ) := by nlinarith
  have hp1 : (2613628740667/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10469747519277/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (352747561981/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (449552733119/1000000000000:ℝ) := by nlinarith
  have hN : (54952499237/100000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (39520006423143/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (54952499237/100000000000:ℝ) (39520006423143/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (60421417/1250000000000:ℝ) ≤ ((54952499237/100000000000:ℝ)/(39520006423143/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_148 (x : ℝ) (h₁ : (4121/2048:ℝ) ≤ x) (h₂ : x ≤ (1031/512:ℝ)) : (60421417/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (95873799/2500000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (429514621/10000000000:ℝ) := by nlinarith
  have hc1 : (999077725489/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (999077725489/1000000000000:ℝ) ≤ taylorCos (429514621/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (62454046847/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (95873799/2500000000:ℝ) + taylorErr ≤ (62454046847/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (19170059007/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (19170059007/500000000000:ℝ) ≤ taylorSin (95873799/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (10734564809/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (429514621/10000000000:ℝ) + taylorErr ≤ (10734564809/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (999077725489/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (62454046847/62500000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (19170059007/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (10734564809/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1580383706719/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6326136769241/1000000000000:ℝ) := by nlinarith
  have hp1 : (41848524683/4000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10469747519277/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (100279835941/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (449552733119/1000000000000:ℝ) := by nlinarith
  have hN : (54952499237/100000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (39520006423143/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (54952499237/100000000000:ℝ) (39520006423143/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (60421417/1250000000000:ℝ) ≤ ((54952499237/100000000000:ℝ)/(39520006423143/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_149 (x : ℝ) (h₁ : (1031/512:ℝ) ≤ x) (h₂ : x ≤ (2065/1024:ℝ)) : (325164291/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (21475731/500000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (130388367/2500000000:ℝ) := by nlinarith
  have hc1 : (998640215917/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (998640215917/1000000000000:ℝ) ≤ taylorCos (130388367/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (999077730017/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (21475731/500000000:ℝ) + taylorErr ≤ (999077730017/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (10734563653/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (10734563653/250000000000:ℝ) ≤ taylorSin (21475731/500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (26065853477/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (130388367/2500000000:ℝ) + taylorErr ≤ (26065853477/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (998640215917/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999077730017/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (10734563653/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (26065853477/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (158153419231/25000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (395958790873/62500000000:ℝ) := by nlinarith
  have hp1 : (5234873689417/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (327655622989/31250000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (17982107147/40000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (34162493839/62500000000:ℝ) := by nlinarith
  have hN : (452040314493/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (1981827060091/25000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (452040314493/1000000000000:ℝ) (1981827060091/25000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (325164291/10000000000000:ℝ) ≤ ((452040314493/1000000000000:ℝ)/(1981827060091/25000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_150 (x : ℝ) (h₁ : (1031/512:ℝ) ≤ x) (h₂ : x ≤ (517/256:ℝ)) : (99255251/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (21475731/500000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (153398079/2500000000:ℝ) := by nlinarith
  have hc1 : (998118110633/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (998118110633/1000000000000:ℝ) ≤ taylorCos (153398079/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (999077730017/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (21475731/500000000:ℝ) + taylorErr ≤ (999077730017/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (10734563653/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (10734563653/250000000000:ℝ) ≤ taylorSin (21475731/500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (61320738649/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (153398079/2500000000:ℝ) + taylorErr ≤ (61320738649/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (998118110633/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999077730017/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (10734563653/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (61320738649/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (158153419231/25000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (793068067337/125000000000:ℝ) := by nlinarith
  have hp1 : (5234873689417/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (525010617601/50000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (17982107147/40000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (321940388699/500000000000:ℝ) := by nlinarith
  have hN : (70847466647/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (15901298161399/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (70847466647/200000000000:ℝ) (15901298161399/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (99255251/5000000000000:ℝ) ≤ ((70847466647/200000000000:ℝ)/(15901298161399/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_151 (x : ℝ) (h₁ : (2065/1024:ℝ) ≤ x) (h₂ : x ≤ (517/256:ℝ)) : (99255251/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (521553467/10000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (153398079/2500000000:ℝ) := by nlinarith
  have hc1 : (998118110633/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (998118110633/1000000000000:ℝ) ≤ taylorCos (153398079/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (998640220447/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (521553467/10000000000:ℝ) + taylorErr ≤ (998640220447/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (5213170233/100000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (5213170233/100000000000:ℝ) ≤ taylorSin (521553467/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (61320738649/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (153398079/2500000000:ℝ) + taylorErr ≤ (61320738649/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (998118110633/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (998640220447/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (5213170233/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (61320738649/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6335340653967/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (793068067337/125000000000:ℝ) := by nlinarith
  have hp1 : (10484979795001/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (525010617601/50000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (546599845609/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (321940388699/500000000000:ℝ) := by nlinarith
  have hN : (70847466647/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (15901298161399/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (70847466647/200000000000:ℝ) (15901298161399/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (99255251/5000000000000:ℝ) ≤ ((70847466647/200000000000:ℝ)/(15901298161399/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_152 (x : ℝ) (h₁ : (517/256:ℝ) ≤ x) (h₂ : x ≤ (1037/512:ℝ)) : (38888271/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/2000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (79767001/1000000000:ℝ) := by nlinarith
  have hc1 : (996820297027/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (996820297027/1000000000000:ℝ) ≤ taylorCos (79767001/1000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (998118115163/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/2000000000:ℝ) + taylorErr ≤ (998118115163/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (2452829361/40000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (2452829361/40000000000:ℝ) ≤ taylorSin (122718463/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (79682440263/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (79767001/1000000000:ℝ) + taylorErr ≤ (79682440263/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (996820297027/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (998118115163/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (2452829361/40000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (79682440263/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1268908907739/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (127259046163/20000000000:ℝ) := by nlinarith
  have hp1 : (10500212211169/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5265338592381/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (643880720207/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (104888756963/125000000000:ℝ) := by nlinarith
  have hN : (157710241323/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (79974324151583/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (157710241323/1000000000000:ℝ) (79974324151583/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (38888271/10000000000000:ℝ) ≤ ((157710241323/1000000000000:ℝ)/(79974324151583/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_153 (x : ℝ) (_h₁ : (517/256:ℝ) ≤ x) (_h₂ : x ≤ (65/32:ℝ)) : (0:ℝ) ≤ wfun x := wfun_nonneg x

theorem wc_154 (x : ℝ) (_h₁ : (1037/512:ℝ) ≤ x) (_h₂ : x ≤ (65/32:ℝ)) : (0:ℝ) ≤ wfun x := wfun_nonneg x

theorem wc_155 (x : ℝ) (h₁ : (65/32:ℝ) ≤ x) (h₂ : x ≤ (263/128:ℝ)) : (2358883/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/1250000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (1718058483/10000000000:ℝ) := by nlinarith
  have hc1 : (985277640117/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (985277640117/1000000000000:ℝ) ≤ taylorCos (1718058483/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (995184728937/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/1250000000:ℝ) + taylorErr ≤ (995184728937/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (98017138043/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (98017138043/1000000000000:ℝ) ≤ taylorSin (122718463/1250000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (85480945539/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1718058483/10000000000:ℝ) + taylorErr ≤ (85480945539/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (985277640117/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (995184728937/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (98017138043/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (85480945539/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1595340019401/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6454991155423/1000000000000:ℝ) := by nlinarith
  have hp1 : (10561141875837/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2670750337119/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (207034580227/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (73055444517/40000000000:ℝ) := by nlinarith
  have hN : (19994086099/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (82333821633179/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (19994086099/500000000000:ℝ) (82333821633179/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2358883/10000000000000:ℝ) ≤ ((19994086099/500000000000:ℝ)/(82333821633179/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_156 (x : ℝ) (h₁ : (65/32:ℝ) ≤ x) (h₂ : x ≤ (529/256:ℝ)) : (1152597/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/1250000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (130388367/625000000:ℝ) := by nlinarith
  have hc1 : (7643104441/7812500000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (7643104441/7812500000:ℝ) ≤ taylorCos (130388367/625000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (995184728937/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/1250000000:ℝ) + taylorErr ≤ (995184728937/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (98017138043/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (98017138043/1000000000000:ℝ) ≤ taylorSin (122718463/1250000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (995184728937/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (98017138043/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (207111378501/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1595340019401/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6491806694333/1000000000000:ℝ) := by nlinarith
  have hp1 : (10561141875837/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10743931013963/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (207034580227/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1112595181411/500000000000:ℝ) := by nlinarith
  have hN : (19994086099/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (41643554156587/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (19994086099/500000000000:ℝ) (41643554156587/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1152597/5000000000000:ℝ) ≤ ((19994086099/500000000000:ℝ)/(41643554156587/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_157 (x : ℝ) (h₁ : (65/32:ℝ) ≤ x) (h₂ : x ≤ (133/64:ℝ)) : (2253027/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/1250000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (2454369261/10000000000:ℝ) := by nlinarith
  have hc1 : (970031250923/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (970031250923/1000000000000:ℝ) ≤ taylorCos (2454369261/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (995184728937/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/1250000000:ℝ) + taylorErr ≤ (995184728937/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (98017138043/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (98017138043/1000000000000:ℝ) ≤ taylorSin (122718463/1250000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (242980182203/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2454369261/10000000000:ℝ) + taylorErr ≤ (242980182203/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (970031250923/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (995184728937/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (98017138043/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (242980182203/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1595340019401/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3264311116621/500000000000:ℝ) := by nlinarith
  have hp1 : (10561141875837/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1350607584931/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (207034580227/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (2625367016571/1000000000000:ℝ) := by nlinarith
  have hN : (19994086099/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (21061454132191/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (19994086099/500000000000:ℝ) (21061454132191/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2253027/10000000000000:ℝ) ≤ ((19994086099/500000000000:ℝ)/(21061454132191/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_158 (x : ℝ) (h₁ : (65/32:ℝ) ≤ x) (h₂ : x ≤ (17/8:ℝ)) : (2058579/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/1250000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (3926990817/10000000000:ℝ) := by nlinarith
  have hc1 : (923879530249/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (923879530249/1000000000000:ℝ) ≤ taylorCos (3926990817/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (995184728937/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/1250000000:ℝ) + taylorErr ≤ (995184728937/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (98017138043/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (98017138043/1000000000000:ℝ) ≤ taylorSin (122718463/1250000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (995184728937/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (98017138043/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (95670858657/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1595340019401/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6675884388879/1000000000000:ℝ) := by nlinarith
  have hp1 : (10561141875837/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1104857934139/100000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (207034580227/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1057027072531/250000000000:ℝ) := by nlinarith
  have hN : (19994086099/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (88134864747357/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (19994086099/500000000000:ℝ) (88134864747357/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2058579/10000000000000:ℝ) ≤ ((19994086099/500000000000:ℝ)/(88134864747357/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_159 (x : ℝ) (h₁ : (523/256:ℝ) ≤ x) (h₂ : x ≤ (529/256:ℝ)) : (6933743/250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1349903093/10000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (130388367/625000000:ℝ) := by nlinarith
  have hc1 : (7643104441/7812500000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (7643104441/7812500000:ℝ) ≤ taylorCos (130388367/625000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (495451318847/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1349903093/10000000000:ℝ) + taylorErr ≤ (495451318847/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (134580706211/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (134580706211/1000000000000:ℝ) ≤ taylorSin (1349903093/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (495451318847/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (134580706211/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (207111378501/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6418175616513/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6491806694333/1000000000000:ℝ) := by nlinarith
  have hp1 : (2124414308101/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10743931013963/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (22336342021/15625000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1112595181411/500000000000:ℝ) := by nlinarith
  have hN : (8772465033/20000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (41643554156587/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (8772465033/20000000000:ℝ) (41643554156587/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (6933743/250000000000:ℝ) ≤ ((8772465033/20000000000:ℝ)/(41643554156587/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_160 (x : ℝ) (h₁ : (263/128:ℝ) ≤ x) (h₂ : x ≤ (133/64:ℝ)) : (996798203/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (859029241/5000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (2454369261/10000000000:ℝ) := by nlinarith
  have hc1 : (970031250923/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (970031250923/1000000000000:ℝ) ≤ taylorCos (2454369261/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (492638822329/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (859029241/5000000000:ℝ) + taylorErr ≤ (492638822329/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (21370235807/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (21370235807/125000000000:ℝ) ≤ taylorSin (859029241/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (242980182203/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2454369261/10000000000:ℝ) + taylorErr ≤ (242980182203/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (970031250923/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (492638822329/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (21370235807/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (242980182203/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3227495577711/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3264311116621/500000000000:ℝ) := by nlinarith
  have hp1 : (2670750301293/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1350607584931/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1826386039047/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (2625367016571/1000000000000:ℝ) := by nlinarith
  have hN : (841108394389/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (21061454132191/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (841108394389/1000000000000:ℝ) (21061454132191/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (996798203/10000000000000:ℝ) ≤ ((841108394389/1000000000000:ℝ)/(21061454132191/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_161 (x : ℝ) (h₁ : (263/128:ℝ) ≤ x) (h₂ : x ≤ (535/256:ℝ)) : (24359219/250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (859029241/5000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (56450493/200000000:ℝ) := by nlinarith
  have hc1 : (192086103429/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (192086103429/200000000000:ℝ) ≤ taylorCos (56450493/200000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (492638822329/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (859029241/5000000000:ℝ) + taylorErr ≤ (492638822329/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (21370235807/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (21370235807/125000000000:ℝ) ≤ taylorSin (859029241/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (11140787667/40000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (56450493/200000000:ℝ) + taylorErr ≤ (11140787667/40000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (192086103429/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (492638822329/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (21370235807/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (11140787667/40000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3227495577711/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6565437772151/1000000000000:ℝ) := by nlinarith
  have hp1 : (2670750301293/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10865790344933/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1826386039047/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (756584144169/250000000000:ℝ) := by nlinarith
  have hN : (841108394389/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (3408397851199/40000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (841108394389/1000000000000:ℝ) (3408397851199/40000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (24359219/250000000000:ℝ) ≤ ((841108394389/1000000000000:ℝ)/(3408397851199/40000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_162 (x : ℝ) (h₁ : (529/256:ℝ) ≤ x) (h₂ : x ≤ (535/256:ℝ)) : (2141232349/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2086213871/10000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (56450493/200000000:ℝ) := by nlinarith
  have hc1 : (192086103429/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (192086103429/200000000000:ℝ) ≤ taylorCos (56450493/200000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (978317372993/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2086213871/10000000000:ℝ) + taylorErr ≤ (978317372993/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (207111373879/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (207111373879/1000000000000:ℝ) ≤ taylorSin (2086213871/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (11140787667/40000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (56450493/200000000:ℝ) + taylorErr ≤ (11140787667/40000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (192086103429/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (978317372993/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (207111373879/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (11140787667/40000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1622951673583/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6565437772151/1000000000000:ℝ) := by nlinarith
  have hp1 : (5371965434921/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10865790344933/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2225190283313/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (756584144169/250000000000:ℝ) := by nlinarith
  have hN : (15585911379/12500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (3408397851199/40000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (15585911379/12500000000:ℝ) (3408397851199/40000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2141232349/10000000000000:ℝ) ≤ ((15585911379/12500000000:ℝ)/(3408397851199/40000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_163 (x : ℝ) (h₁ : (529/256:ℝ) ≤ x) (h₂ : x ≤ (269/128:ℝ)) : (523331013/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2086213871/10000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (3190680039/10000000000:ℝ) := by nlinarith
  have hc1 : (37981127133/40000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (37981127133/40000000000:ℝ) ≤ taylorCos (3190680039/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (978317372993/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2086213871/10000000000:ℝ) + taylorErr ≤ (978317372993/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (207111373879/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (207111373879/1000000000000:ℝ) ≤ taylorSin (2086213871/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (7842043567/25000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3190680039/10000000000:ℝ) + taylorErr ≤ (7842043567/25000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (37981127133/40000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (978317372993/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (207111373879/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (7842043567/25000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1622951673583/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (330112665553/50000000000:ℝ) := by nlinarith
  have hp1 : (5371965434921/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5463360005209/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2225190283313/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (685502514929/200000000000:ℝ) := by nlinarith
  have hN : (15585911379/12500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (43089748783403/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (15585911379/12500000000:ℝ) (43089748783403/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (523331013/2500000000000:ℝ) ≤ ((15585911379/12500000000:ℝ)/(43089748783403/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_164 (x : ℝ) (h₁ : (133/64:ℝ) ≤ x) (h₂ : x ≤ (17/8:ℝ)) : (141103133/400000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/500000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (3926990817/10000000000:ℝ) := by nlinarith
  have hc1 : (923879530249/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (923879530249/1000000000000:ℝ) ≤ taylorCos (3926990817/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (60626953467/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/500000000:ℝ) + taylorErr ≤ (60626953467/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (242980177581/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (242980177581/1000000000000:ℝ) ≤ taylorSin (122718463/500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (60626953467/62500000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (242980177581/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (95670858657/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6528622233241/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6675884388879/1000000000000:ℝ) := by nlinarith
  have hp1 : (1080486053451/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1104857934139/100000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2625366931413/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1057027072531/250000000000:ℝ) := by nlinarith
  have hN : (1655335675941/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (88134864747357/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1655335675941/1000000000000:ℝ) (88134864747357/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (141103133/400000000000:ℝ) ≤ ((1655335675941/1000000000000:ℝ)/(88134864747357/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_165 (x : ℝ) (h₁ : (133/64:ℝ) ≤ x) (h₂ : x ≤ (139/64:ℝ)) : (3229627133/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/500000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (2699806187/5000000000:ℝ) := by nlinarith
  have hc1 : (107216075963/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (107216075963/125000000000:ℝ) ≤ taylorCos (2699806187/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (60626953467/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/500000000:ℝ) + taylorErr ≤ (60626953467/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (242980177581/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (242980177581/1000000000000:ℝ) ≤ taylorSin (122718463/500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (51410274651/100000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2699806187/5000000000:ℝ) + taylorErr ≤ (51410274651/100000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (107216075963/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (60626953467/62500000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (242980177581/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (51410274651/100000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6528622233241/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1705786636129/250000000000:ℝ) := by nlinarith
  have hp1 : (1080486053451/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (11292298003333/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2625366931413/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (5805401417923/1000000000000:ℝ) := by nlinarith
  have hN : (1655335675941/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (46055328767941/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1655335675941/1000000000000:ℝ) (46055328767941/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (3229627133/10000000000000:ℝ) ≤ ((1655335675941/1000000000000:ℝ)/(46055328767941/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_166 (x : ℝ) (h₁ : (17/8:ℝ) ≤ x) (h₂ : x ≤ (137/64:ℝ)) : (13645037373/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/312500000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (441786467/1000000000:ℝ) := by nlinarith
  have hc1 : (903989290823/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (903989290823/1000000000000:ℝ) ≤ taylorCos (441786467/1000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (923879534811/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/312500000:ℝ) + taylorErr ≤ (923879534811/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (95670857503/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (95670857503/250000000000:ℝ) ≤ taylorSin (122718463/312500000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (427555095773/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (441786467/1000000000:ℝ) + taylorErr ≤ (427555095773/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (903989290823/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (923879534811/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (95670857503/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (427555095773/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3337942194439/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6724971774091/1000000000000:ℝ) := by nlinarith
  have hp1 : (11048579193183/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (11129818895371/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2114054091203/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (4758610783747/1000000000000:ℝ) := by nlinarith
  have hN : (660845729519/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (44725245362321/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (660845729519/200000000000:ℝ) (44725245362321/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (13645037373/10000000000000:ℝ) ≤ ((660845729519/200000000000:ℝ)/(44725245362321/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_167 (x : ℝ) (h₁ : (17/8:ℝ) ≤ x) (h₂ : x ≤ (71/32:ℝ)) : (18443873/15625000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/312500000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (687223393/1000000000:ℝ) := by nlinarith
  have hc1 : (38650522553/50000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (38650522553/50000000000:ℝ) ≤ taylorCos (687223393/1000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (923879534811/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/312500000:ℝ) + taylorErr ≤ (923879534811/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (95670857503/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (95670857503/250000000000:ℝ) ≤ taylorSin (122718463/312500000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (317196643223/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (687223393/1000000000:ℝ) + taylorErr ≤ (317196643223/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (38650522553/50000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (923879534811/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (95670857503/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (317196643223/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3337942194439/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6970408700153/1000000000000:ℝ) := by nlinarith
  have hp1 : (11048579193183/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (461440666611/40000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2114054091203/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (365918576239/50000000000:ℝ) := by nlinarith
  have hN : (660845729519/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (48086597447169/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (660845729519/200000000000:ℝ) (48086597447169/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (18443873/15625000000:ℝ) ≤ ((660845729519/200000000000:ℝ)/(48086597447169/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_168 (x : ℝ) (h₁ : (137/64:ℝ) ≤ x) (h₂ : x ≤ (69/32:ℝ)) : (9015580911/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (4417864669/10000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (2454369261/5000000000:ℝ) := by nlinarith
  have hc1 : (17638425241/20000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (17638425241/20000000000:ℝ) ≤ taylorCos (2454369261/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (90398929539/100000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (4417864669/10000000000:ℝ) + taylorErr ≤ (90398929539/100000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (213777545579/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (213777545579/500000000000:ℝ) ≤ taylorSin (4417864669/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (117849184789/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2454369261/5000000000:ℝ) + taylorErr ≤ (117849184789/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (17638425241/20000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (90398929539/100000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (213777545579/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (117849184789/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (672497177409/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6774059159303/1000000000000:ℝ) := by nlinarith
  have hp1 : (11129818746073/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (11211058449351/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4758610668549/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (660607049439/125000000000:ℝ) := by nlinarith
  have hN : (3854621373159/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (45387877493737/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3854621373159/1000000000000:ℝ) (45387877493737/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (9015580911/5000000000000:ℝ) ≤ ((3854621373159/1000000000000:ℝ)/(45387877493737/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_169 (x : ℝ) (h₁ : (69/32:ℝ) ≤ x) (h₂ : x ≤ (35/16:ℝ)) : (4439229703/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (4908738521/10000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (2945243113/5000000000:ℝ) := by nlinarith
  have hc1 : (103933701251/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (103933701251/125000000000:ℝ) ≤ taylorCos (2945243113/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (881921266621/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (4908738521/10000000000:ℝ) + taylorErr ≤ (881921266621/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (471396734543/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (471396734543/1000000000000:ℝ) ≤ taylorSin (4908738521/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (22222809413/40000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2945243113/5000000000:ℝ) + taylorErr ≤ (22222809413/40000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (103933701251/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (881921266621/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (471396734543/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (22222809413/40000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3387029579651/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6711165947/976562500:ℝ) := by nlinarith
  have hp1 : (2802764574741/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (11373537557313/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2642428136451/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1263759787439/200000000000:ℝ) := by nlinarith
  have hN : (4402935006281/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (9345519836981/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4402935006281/1000000000000:ℝ) (9345519836981/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (4439229703/2000000000000:ℝ) ≤ ((4402935006281/1000000000000:ℝ)/(9345519836981/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_170 (x : ℝ) (h₁ : (35/16:ℝ) ≤ x) (h₂ : x ≤ (9/4:ℝ)) : (3845725361/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (235619449/400000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (207867403647/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (235619449/400000000:ℝ) + taylorErr ≤ (207867403647/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (555570230717/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (555570230717/1000000000000:ℝ) ≤ taylorSin (235619449/400000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (207867403647/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (555570230717/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (176776695861/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6872233929727/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3534291735289/500000000000:ℝ) := by nlinarith
  have hp1 : (11373537404747/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (11698495773237/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (6318798800023/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (8272085717347/1000000000000:ℝ) := by nlinarith
  have hN : (1097465837087/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (49464872280529/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1097465837087/200000000000:ℝ) (49464872280529/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (3845725361/1250000000000:ℝ) ≤ ((1097465837087/200000000000:ℝ)/(49464872280529/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_171 (x : ℝ) (h₁ : (9/4:ℝ) ≤ x) (h₂ : x ≤ (5/2:ℝ)) : (38217750111/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * ((5/2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((5/2:ℝ) - x) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * ((5/2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((5/2:ℝ) - x)) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * ((5/2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((5/2:ℝ) - x)) ≤ (176776695861/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/5000000000:ℝ) + taylorErr ≤ (176776695861/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * ((5/2:ℝ) - x)) := by
    have h := (trig_shift (5/2:ℝ) (x - (5/2:ℝ))).1
    rw [show (5/2:ℝ) + (x - (5/2:ℝ)) = x by ring, cs_h5.1, cs_h5.2] at h
    rw [h, cos_flip (5/2:ℝ) x, sin_flip (5/2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((5/2:ℝ) - x)) := by
    have h := (trig_shift (5/2:ℝ) (x - (5/2:ℝ))).2
    rw [show (5/2:ℝ) + (x - (5/2:ℝ)) = x by ring, cs_h5.1, cs_h5.2] at h
    rw [h, cos_flip (5/2:ℝ) x, sin_flip (5/2:ℝ) x]; ring
  have hcxl : (-1131/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (176776695861/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (88388347351/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (500000001131/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7068583470577/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (314159265359/40000000000:ℝ) := by nlinarith
  have hp1 : (1462311952039/125000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (12998328636929/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (8272085552149/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (3249582166583/250000000000:ℝ) := by nlinarith
  have hN : (1512995753741/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (61185027506817/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1512995753741/200000000000:ℝ) (61185027506817/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (38217750111/10000000000000:ℝ) ≤ ((1512995753741/200000000000:ℝ)/(61185027506817/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_172 (x : ℝ) (h₁ : (5/2:ℝ) ≤ x) (h₂ : x ≤ (11/4:ℝ)) : (38423148027/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * (x - (5/2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5/2:ℝ)) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5/2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5/2:ℝ))) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5/2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5/2:ℝ))) ≤ (176776695861/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/5000000000:ℝ) + taylorErr ≤ (176776695861/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5/2:ℝ))) := by
    have h := (trig_shift (5/2:ℝ) (x - (5/2:ℝ))).1
    rw [show (5/2:ℝ) + (x - (5/2:ℝ)) = x by ring, cs_h5.1, cs_h5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (5/2:ℝ))) := by
    have h := (trig_shift (5/2:ℝ) (x - (5/2:ℝ))).2
    rw [show (5/2:ℝ) + (x - (5/2:ℝ)) = x by ring, cs_h5.1, cs_h5.2] at h
    rw [h]; ring
  have hcxl : (-176776695861/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (1131/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (88388347351/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (500000001131/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3926990816987/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2159844949343/250000000000:ℝ) := by nlinarith
  have hp1 : (1624791057821/125000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (14298161500621/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4595603084527/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (3574540383241/250000000000:ℝ) := by nlinarith
  have hN : (1148900770849/125000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (148277766566479/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1148900770849/125000000000:ℝ) (148277766566479/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (38423148027/10000000000000:ℝ) ≤ ((1148900770849/125000000000:ℝ)/(148277766566479/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_173 (x : ℝ) (h₁ : (11/4:ℝ) ≤ x) (h₂ : x ≤ (23/8:ℝ)) : (14518912047/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/312500000:ℝ) ≤ Real.pi * ((3:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((3:ℝ) - x) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((3:ℝ) - x)) ≤ (923879534811/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/312500000:ℝ) + taylorErr ≤ (923879534811/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (95670857503/250000000000:ℝ) ≤ Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (95670857503/250000000000:ℝ) ≤ taylorSin (122718463/312500000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((3:ℝ) - x)) ≤ (176776695861/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/5000000000:ℝ) + taylorErr ≤ (176776695861/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h, cos_flip (3:ℝ) x, sin_flip (3:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h, cos_flip (3:ℝ) x, sin_flip (3:ℝ) x]; ring
  have hcxl : (-923879534811/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-88388347351/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (95670857503/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (176776695861/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (8639379797371/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9032078879071/1000000000000:ℝ) := by nlinarith
  have hp1 : (1787270163603/125000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3737019483117/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (218866776501/40000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (5284943652749/500000000000:ℝ) := by nlinarith
  have hN : (6178776191333/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (162156897755521/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (6178776191333/1000000000000:ℝ) (162156897755521/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (14518912047/10000000000000:ℝ) ≤ ((6178776191333/1000000000000:ℝ)/(162156897755521/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_174 (x : ℝ) (h₁ : (23/8:ℝ) ≤ x) (h₂ : x ≤ (755/256:ℝ)) : (233399711/625000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1595340019/10000000000:ℝ) ≤ Real.pi * ((3:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((3:ℝ) - x) ≤ (3926990817/10000000000:ℝ) := by nlinarith
  have hc1 : (923879530249/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (923879530249/1000000000000:ℝ) ≤ taylorCos (3926990817/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((3:ℝ) - x)) ≤ (493650710213/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1595340019/10000000000:ℝ) + taylorErr ≤ (493650710213/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (19857267629/125000000000:ℝ) ≤ Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (19857267629/125000000000:ℝ) ≤ taylorSin (1595340019/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((3:ℝ) - x)) ≤ (95670858657/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/10000000000:ℝ) + taylorErr ≤ (95670858657/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h, cos_flip (3:ℝ) x, sin_flip (3:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h, cos_flip (3:ℝ) x, sin_flip (3:ℝ) x]; ring
  have hcxl : (-493650710213/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-923879530249/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (19857267629/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (95670858657/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (903207887907/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (926524395883/100000000000:ℝ) := by nlinarith
  have hp1 : (14948077731953/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15333965813877/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2374623840499/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (5868054704123/1000000000000:ℝ) := by nlinarith
  have hN : (824625842687/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (21336186404159/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (824625842687/250000000000:ℝ) (21336186404159/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (233399711/625000000000:ℝ) ≤ ((824625842687/250000000000:ℝ)/(21336186404159/125000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_175 (x : ℝ) (h₁ : (755/256:ℝ) ≤ x) (h₂ : x ≤ (1529/512:ℝ)) : (44199559/500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (21475731/500000000:ℝ) ≤ Real.pi * ((3:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((3:ℝ) - x) ≤ (79767001/500000000:ℝ) := by nlinarith
  have hc1 : (493650707943/500000000000:ℝ) ≤ Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (493650707943/500000000000:ℝ) ≤ taylorCos (79767001/500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((3:ℝ) - x)) ≤ (999077730017/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (21475731/500000000:ℝ) + taylorErr ≤ (999077730017/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (10734563653/250000000000:ℝ) ≤ Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (10734563653/250000000000:ℝ) ≤ taylorSin (21475731/500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((3:ℝ) - x)) ≤ (31771629131/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (79767001/500000000:ℝ) + taylorErr ≤ (31771629131/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h, cos_flip (3:ℝ) x, sin_flip (3:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h, cos_flip (3:ℝ) x, sin_flip (3:ℝ) x]; ring
  have hcxl : (-999077730017/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-493650707943/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (10734563653/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (31771629131/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9265243958829/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9381826498709/1000000000000:ℝ) := by nlinarith
  have hp1 : (7666982804093/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15526909754581/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (131682743899/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1233288045683/500000000000:ℝ) := by nlinarith
  have hN : (1645715135381/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (175037336903757/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1645715135381/1000000000000:ℝ) (175037336903757/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (44199559/500000000000:ℝ) ≤ ((1645715135381/1000000000000:ℝ)/(175037336903757/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_176 (x : ℝ) (h₁ : (755/256:ℝ) ≤ x) (h₂ : x ≤ (3:ℝ)) : (156180947/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * ((3:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((3:ℝ) - x) ≤ (79767001/500000000:ℝ) := by nlinarith
  have hc1 : (493650707943/500000000000:ℝ) ≤ Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (493650707943/500000000000:ℝ) ≤ taylorCos (79767001/500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((3:ℝ) - x)) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((3:ℝ) - x)) ≤ (31771629131/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (79767001/500000000:ℝ) + taylorErr ≤ (31771629131/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h, cos_flip (3:ℝ) x, sin_flip (3:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h, cos_flip (3:ℝ) x, sin_flip (3:ℝ) x]; ring
  have hcxl : (-500000001131/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-493650707943/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (31771629131/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9265243958829/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (942477796077/100000000000:ℝ) := by nlinarith
  have hp1 : (7666982804093/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3119598872863/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-35283/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (2477868460653/1000000000000:ℝ) := by nlinarith
  have hN : (987301380603/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (11040804951227/62500000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (987301380603/1000000000000:ℝ) (11040804951227/62500000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (156180947/5000000000000:ℝ) ≤ ((987301380603/1000000000000:ℝ)/(11040804951227/62500000000:ℝ))^2 := by norm_num
  linarith

theorem wc_177 (x : ℝ) (h₁ : (189/64:ℝ) ≤ x) (h₂ : x ≤ (3:ℝ)) : (156774751/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * ((3:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((3:ℝ) - x) ≤ (1472621557/10000000000:ℝ) := by nlinarith
  have hc1 : (989176507693/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (989176507693/1000000000000:ℝ) ≤ taylorCos (1472621557/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((3:ℝ) - x)) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((3:ℝ) - x)) ≤ (7336523839/50000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1472621557/10000000000:ℝ) + taylorErr ≤ (7336523839/50000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h, cos_flip (3:ℝ) x, sin_flip (3:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h, cos_flip (3:ℝ) x, sin_flip (3:ℝ) x]; ring
  have hcxl : (-500000001131/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-989176507693/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (7336523839/50000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (2319378951283/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (942477796077/100000000000:ℝ) := by nlinarith
  have hp1 : (15354275496409/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3119598872863/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-35283/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (35760955467/15625000000:ℝ) := by nlinarith
  have hN : (98917647241/100000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (11040804951227/62500000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (98917647241/100000000000:ℝ) (11040804951227/62500000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (156774751/5000000000000:ℝ) ≤ ((98917647241/100000000000:ℝ)/(11040804951227/62500000000:ℝ))^2 := by norm_num
  linarith

theorem wc_178 (x : ℝ) (h₁ : (1529/512:ℝ) ≤ x) (h₂ : x ≤ (3:ℝ)) : (3198579/100000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * ((3:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((3:ℝ) - x) ≤ (429514621/10000000000:ℝ) := by nlinarith
  have hc1 : (999077725489/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (999077725489/1000000000000:ℝ) ≤ taylorCos (429514621/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((3:ℝ) - x)) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((3:ℝ) - x)) ≤ (10734564809/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (429514621/10000000000:ℝ) + taylorErr ≤ (10734564809/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h, cos_flip (3:ℝ) x, sin_flip (3:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h, cos_flip (3:ℝ) x, sin_flip (3:ℝ) x]; ring
  have hcxl : (-500000001131/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-999077725489/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (10734564809/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (2345456624677/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (942477796077/100000000000:ℝ) := by nlinarith
  have hp1 : (7763454773151/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3119598872863/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-35283/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (669750725577/1000000000000:ℝ) := by nlinarith
  have hN : (499538845103/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (11040804951227/62500000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (499538845103/500000000000:ℝ) (11040804951227/62500000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (3198579/100000000000:ℝ) ≤ ((499538845103/500000000000:ℝ)/(11040804951227/62500000000:ℝ))^2 := by norm_num
  linarith

theorem wc_179 (x : ℝ) (_h₁ : (3:ℝ) ≤ x) (_h₂ : x ≤ (387/128:ℝ)) : (0:ℝ) ≤ wfun x := wfun_nonneg x

end Zeta23Ext.Bridge.ThreePoint
