import FourPoint.Base

noncomputable section
open Real
namespace Zeta23Ext.Bridge.FourPoint


theorem wc_600 (x : ℝ) (h₁ : (791/256:ℝ) ≤ x) (h₂ : x ≤ (811/256:ℝ)) : (1589247651/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2822524649/10000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (5276893911/10000000000:ℝ) := by nlinarith
  have hc1 : (34558914153/40000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (34558914153/40000000000:ℝ) ≤ taylorCos (5276893911/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (960430521697/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2822524649/10000000000:ℝ) + taylorErr ≤ (960430521697/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (55703937411/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (55703937411/200000000000:ℝ) ≤ taylorSin (2822524649/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (251769193023/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (5276893911/10000000000:ℝ) + taylorErr ≤ (251769193023/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-960430521697/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-34558914153/40000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-251769193023/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-55703937411/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (485351521287/50000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9952467351803/1000000000000:ℝ) := by nlinarith
  have hp1 : (8032560792103/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (16471319569609/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-8293941672129/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-4474452636133/1000000000000:ℝ) := by nlinarith
  have hN : (878505528609/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (19710321277741/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (878505528609/250000000000:ℝ) (19710321277741/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1589247651/5000000000000:ℝ) ≤ ((878505528609/250000000000:ℝ)/(19710321277741/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_601 (x : ℝ) (h₁ : (791/256:ℝ) ≤ x) (h₂ : x ≤ (51/16:ℝ)) : (3100919687/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2822524649/10000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (2945243113/5000000000:ℝ) := by nlinarith
  have hc1 : (103933701251/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (103933701251/125000000000:ℝ) ≤ taylorCos (2945243113/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (960430521697/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2822524649/10000000000:ℝ) + taylorErr ≤ (960430521697/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (55703937411/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (55703937411/200000000000:ℝ) ≤ taylorSin (2822524649/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (22222809413/40000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2945243113/5000000000:ℝ) + taylorErr ≤ (22222809413/40000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-960430521697/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-103933701251/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-22222809413/40000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-55703937411/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (485351521287/50000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (5006913291659/500000000000:ℝ) := by nlinarith
  have hp1 : (8032560792103/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (4143217253021/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-4603696368527/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-4474452636133/1000000000000:ℝ) := by nlinarith
  have hN : (878505528609/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (199553445681533/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (878505528609/250000000000:ℝ) (199553445681533/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (3100919687/10000000000000:ℝ) ≤ ((878505528609/250000000000:ℝ)/(199553445681533/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_602 (x : ℝ) (h₁ : (1587/512:ℝ) ≤ x) (h₂ : x ≤ (809/256:ℝ)) : (2090005161/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (3129320807/10000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (1006291397/2000000000:ℝ) := by nlinarith
  have hc1 : (876070091897/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (876070091897/1000000000000:ℝ) ≤ taylorCos (1006291397/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (23785875581/25000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (3129320807/10000000000:ℝ) + taylorErr ≤ (23785875581/25000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (38481204719/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (38481204719/125000000000:ℝ) ≤ taylorSin (3129320807/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (241091887203/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1006291397/2000000000:ℝ) + taylorErr ≤ (241091887203/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-23785875581/25000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-876070091897/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-241091887203/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-38481204719/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (4868855020749/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2481980914799/250000000000:ℝ) := by nlinarith
  have hp1 : (16115896304763/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (16430699792617/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-990327105267/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-496127283947/100000000000:ℝ) := by nlinarith
  have hN : (400983781623/100000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (12257958522853/62500000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (400983781623/100000000000:ℝ) (12257958522853/62500000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2090005161/5000000000000:ℝ) ≤ ((400983781623/100000000000:ℝ)/(12257958522853/62500000000:ℝ))^2 := by norm_num
  linarith

theorem wc_603 (x : ℝ) (h₁ : (199/64:ℝ) ≤ x) (h₂ : x ≤ (811/256:ℝ)) : (5223624809/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (859029241/2500000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (5276893911/10000000000:ℝ) := by nlinarith
  have hc1 : (34558914153/40000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (34558914153/40000000000:ℝ) ≤ taylorCos (5276893911/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (470772033737/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (859029241/2500000000:ℝ) + taylorErr ≤ (470772033737/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (336889851049/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (336889851049/1000000000000:ℝ) ≤ taylorSin (859029241/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (251769193023/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (5276893911/10000000000:ℝ) + taylorErr ≤ (251769193023/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-470772033737/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-34558914153/40000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-251769193023/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-336889851049/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1953677931451/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9952467351803/1000000000000:ℝ) := by nlinarith
  have hp1 : (16166671025319/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (16471319569609/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-8293941672129/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-5446387393677/1000000000000:ℝ) := by nlinarith
  have hN : (4504843326203/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (19710321277741/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4504843326203/1000000000000:ℝ) (19710321277741/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (5223624809/10000000000000:ℝ) ≤ ((4504843326203/1000000000000:ℝ)/(19710321277741/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_604 (x : ℝ) (h₁ : (199/64:ℝ) ≤ x) (h₂ : x ≤ (51/16:ℝ)) : (5096134953/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (859029241/2500000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (2945243113/5000000000:ℝ) := by nlinarith
  have hc1 : (103933701251/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (103933701251/125000000000:ℝ) ≤ taylorCos (2945243113/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (470772033737/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (859029241/2500000000:ℝ) + taylorErr ≤ (470772033737/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (336889851049/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (336889851049/1000000000000:ℝ) ≤ taylorSin (859029241/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (22222809413/40000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2945243113/5000000000:ℝ) + taylorErr ≤ (22222809413/40000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-470772033737/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-103933701251/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-22222809413/40000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-336889851049/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1953677931451/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (5006913291659/500000000000:ℝ) := by nlinarith
  have hp1 : (16166671025319/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (4143217253021/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-4603696368527/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-5446387393677/1000000000000:ℝ) := by nlinarith
  have hN : (4504843326203/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (199553445681533/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4504843326203/1000000000000:ℝ) (199553445681533/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (5096134953/10000000000000:ℝ) ≤ ((4504843326203/1000000000000:ℝ)/(199553445681533/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_605 (x : ℝ) (h₁ : (199/64:ℝ) ≤ x) (h₂ : x ≤ (413/128:ℝ)) : (37911123/78125000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (859029241/2500000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (889708857/1250000000:ℝ) := by nlinarith
  have hc1 : (151441768839/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (151441768839/200000000000:ℝ) ≤ taylorCos (889708857/1250000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (470772033737/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (859029241/2500000000:ℝ) + taylorErr ≤ (470772033737/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (336889851049/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (336889851049/1000000000000:ℝ) ≤ taylorSin (859029241/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (65317284523/100000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (889708857/1250000000:ℝ) + taylorErr ≤ (65317284523/100000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-470772033737/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-151441768839/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-65317284523/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-336889851049/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1953677931451/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (10136545046349/1000000000000:ℝ) := by nlinarith
  have hp1 : (16166671025319/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (16775967897037/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2191521336559/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-5446387393677/1000000000000:ℝ) := by nlinarith
  have hN : (4504843326203/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (8179963638133/40000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4504843326203/1000000000000:ℝ) (8179963638133/40000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (37911123/78125000000:ℝ) ≤ ((4504843326203/1000000000000:ℝ)/(8179963638133/40000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_606 (x : ℝ) (h₁ : (199/64:ℝ) ≤ x) (h₂ : x ≤ (13/4:ℝ)) : (589186081/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (859029241/2500000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (470772033737/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (859029241/2500000000:ℝ) + taylorErr ≤ (470772033737/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (336889851049/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (336889851049/1000000000000:ℝ) ≤ taylorSin (859029241/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (176776695861/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/5000000000:ℝ) + taylorErr ≤ (176776695861/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-470772033737/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-88388347351/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-176776695861/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-336889851049/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1953677931451/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (10210176124167/1000000000000:ℝ) := by nlinarith
  have hp1 : (16166671025319/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (16897827228007/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-11948568258389/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-5446387393677/1000000000000:ℝ) := by nlinarith
  have hN : (4504843326203/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10374769648651/50000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4504843326203/1000000000000:ℝ) (10374769648651/50000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (589186081/1250000000000:ℝ) ≤ ((4504843326203/1000000000000:ℝ)/(10374769648651/50000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_607 (x : ℝ) (h₁ : (403/128:ℝ) ≤ x) (h₂ : x ≤ (13/4:ℝ)) : (9713220361/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (932660319/2000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (178644860693/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (932660319/2000000000:ℝ) + taylorErr ≤ (178644860693/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (449611327377/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (449611327377/1000000000000:ℝ) ≤ taylorSin (932660319/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (176776695861/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/5000000000:ℝ) + taylorErr ≤ (176776695861/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-178644860693/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-88388347351/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-176776695861/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-449611327377/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (4945554060143/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (10210176124167/1000000000000:ℝ) := by nlinarith
  have hp1 : (16369769907547/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (16897827228007/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-11948568258389/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1840008494247/250000000000:ℝ) := by nlinarith
  have hN : (6466809673523/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10374769648651/50000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (6466809673523/1000000000000:ℝ) (10374769648651/50000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (9713220361/10000000000000:ℝ) ≤ ((6466809673523/1000000000000:ℝ)/(10374769648651/50000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_608 (x : ℝ) (h₁ : (809/256:ℝ) ≤ x) (h₂ : x ≤ (13/4:ℝ)) : (11532825879/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (628932123/1250000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (87607009647/100000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (628932123/1250000000:ℝ) + taylorErr ≤ (87607009647/100000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (241091884897/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (241091884897/500000000000:ℝ) ≤ taylorSin (628932123/1250000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (176776695861/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/5000000000:ℝ) + taylorErr ≤ (176776695861/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-87607009647/100000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-88388347351/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-176776695861/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-241091884897/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1985584731839/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (10210176124167/1000000000000:ℝ) := by nlinarith
  have hp1 : (3286139914443/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (16897827228007/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-11948568258389/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-7922616660083/1000000000000:ℝ) := by nlinarith
  have hN : (7046546563613/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10374769648651/50000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (7046546563613/1000000000000:ℝ) (10374769648651/50000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (11532825879/10000000000000:ℝ) ≤ ((7046546563613/1000000000000:ℝ)/(10374769648651/50000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_609 (x : ℝ) (h₁ : (13/4:ℝ) ≤ x) (h₂ : x ≤ (209/64:ℝ)) : (1799437923/625000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (7363107781/10000000000:ℝ) ≤ Real.pi * ((7/2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((7/2:ℝ) - x) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * ((7/2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((7/2:ℝ) - x)) ≤ (740951127621/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (7363107781/10000000000:ℝ) + taylorErr ≤ (740951127621/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (671558952519/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((7/2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (671558952519/1000000000000:ℝ) ≤ taylorSin (7363107781/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((7/2:ℝ) - x)) ≤ (176776695861/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/5000000000:ℝ) + taylorErr ≤ (176776695861/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((7/2:ℝ) - x)) := by
    have h := (trig_shift (7/2:ℝ) (x - (7/2:ℝ))).1
    rw [show (7/2:ℝ) + (x - (7/2:ℝ)) = x by ring, cs_h7.1, cs_h7.2] at h
    rw [h, cos_flip (7/2:ℝ) x, sin_flip (7/2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((7/2:ℝ) - x)) := by
    have h := (trig_shift (7/2:ℝ) (x - (7/2:ℝ))).2
    rw [show (7/2:ℝ) + (x - (7/2:ℝ)) = x by ring, cs_h7.1, cs_h7.2] at h
    rw [h, cos_flip (7/2:ℝ) x, sin_flip (7/2:ℝ) x]; ring
  have hcxl : (-176776695861/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-671558952519/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-740951127621/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-88388347351/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (5105088062083/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (512963175469/50000000000:ℝ) := by nlinarith
  have hp1 : (8448913500669/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (16979066781989/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-3145164669517/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1194856801977/100000000000:ℝ) := by nlinarith
  have hN : (5620730618163/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (209504975509793/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (5620730618163/500000000000:ℝ) (209504975509793/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1799437923/625000000000:ℝ) ≤ ((5620730618163/500000000000:ℝ)/(209504975509793/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_610 (x : ℝ) (h₁ : (13/4:ℝ) ≤ x) (h₂ : x ≤ (105/32:ℝ)) : (7060987389/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (6872233929/10000000000:ℝ) ≤ Real.pi * ((7/2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((7/2:ℝ) - x) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * ((7/2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((7/2:ℝ) - x)) ≤ (24156576739/31250000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (6872233929/10000000000:ℝ) + taylorErr ≤ (24156576739/31250000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (158598320461/250000000000:ℝ) ≤ Real.sin (Real.pi * ((7/2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (158598320461/250000000000:ℝ) ≤ taylorSin (6872233929/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((7/2:ℝ) - x)) ≤ (176776695861/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/5000000000:ℝ) + taylorErr ≤ (176776695861/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((7/2:ℝ) - x)) := by
    have h := (trig_shift (7/2:ℝ) (x - (7/2:ℝ))).1
    rw [show (7/2:ℝ) + (x - (7/2:ℝ)) = x by ring, cs_h7.1, cs_h7.2] at h
    rw [h, cos_flip (7/2:ℝ) x, sin_flip (7/2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((7/2:ℝ) - x)) := by
    have h := (trig_shift (7/2:ℝ) (x - (7/2:ℝ))).2
    rw [show (7/2:ℝ) + (x - (7/2:ℝ)) = x by ring, cs_h7.1, cs_h7.2] at h
    rw [h, cos_flip (7/2:ℝ) x, sin_flip (7/2:ℝ) x]; ring
  have hcxl : (-176776695861/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-158598320461/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-24156576739/31250000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-88388347351/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (5105088062083/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (20133497841/1953125000:ℝ) := by nlinarith
  have hp1 : (8448913500669/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (17060306335969/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-6593897587131/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1194856801977/100000000000:ℝ) := by nlinarith
  have hN : (5620730618163/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (26440524541509/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (5620730618163/500000000000:ℝ) (26440524541509/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (7060987389/2500000000000:ℝ) ≤ ((5620730618163/500000000000:ℝ)/(26440524541509/125000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_611 (x : ℝ) (h₁ : (13/4:ℝ) ≤ x) (h₂ : x ≤ (423/128:ℝ)) : (27447518209/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (6135923151/10000000000:ℝ) ≤ Real.pi * ((7/2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((7/2:ℝ) - x) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * ((7/2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((7/2:ℝ) - x)) ≤ (817584815439/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (6135923151/10000000000:ℝ) + taylorErr ≤ (817584815439/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (575808189111/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((7/2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (575808189111/1000000000000:ℝ) ≤ taylorSin (6135923151/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((7/2:ℝ) - x)) ≤ (176776695861/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/5000000000:ℝ) + taylorErr ≤ (176776695861/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((7/2:ℝ) - x)) := by
    have h := (trig_shift (7/2:ℝ) (x - (7/2:ℝ))).1
    rw [show (7/2:ℝ) + (x - (7/2:ℝ)) = x by ring, cs_h7.1, cs_h7.2] at h
    rw [h, cos_flip (7/2:ℝ) x, sin_flip (7/2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((7/2:ℝ) - x)) := by
    have h := (trig_shift (7/2:ℝ) (x - (7/2:ℝ))).2
    rw [show (7/2:ℝ) + (x - (7/2:ℝ)) = x by ring, cs_h7.1, cs_h7.2] at h
    rw [h, cos_flip (7/2:ℝ) x, sin_flip (7/2:ℝ) x]; ring
  have hcxl : (-176776695861/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-575808189111/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-817584815439/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-88388347351/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (5105088062083/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (10381981972411/1000000000000:ℝ) := by nlinarith
  have hp1 : (8448913500669/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (17182165666941/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-14047877745649/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1194856801977/100000000000:ℝ) := by nlinarith
  have hN : (5620730618163/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (107285549675467/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (5620730618163/500000000000:ℝ) (107285549675467/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (27447518209/10000000000000:ℝ) ≤ ((5620730618163/500000000000:ℝ)/(107285549675467/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_612 (x : ℝ) (h₁ : (13/4:ℝ) ≤ x) (h₂ : x ≤ (107/32:ℝ)) : (5236311191/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (4908738521/10000000000:ℝ) ≤ Real.pi * ((7/2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((7/2:ℝ) - x) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * ((7/2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((7/2:ℝ) - x)) ≤ (881921266621/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (4908738521/10000000000:ℝ) + taylorErr ≤ (881921266621/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (471396734543/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((7/2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (471396734543/1000000000000:ℝ) ≤ taylorSin (4908738521/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((7/2:ℝ) - x)) ≤ (176776695861/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/5000000000:ℝ) + taylorErr ≤ (176776695861/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((7/2:ℝ) - x)) := by
    have h := (trig_shift (7/2:ℝ) (x - (7/2:ℝ))).1
    rw [show (7/2:ℝ) + (x - (7/2:ℝ)) = x by ring, cs_h7.1, cs_h7.2] at h
    rw [h, cos_flip (7/2:ℝ) x, sin_flip (7/2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((7/2:ℝ) - x)) := by
    have h := (trig_shift (7/2:ℝ) (x - (7/2:ℝ))).2
    rw [show (7/2:ℝ) + (x - (7/2:ℝ)) = x by ring, cs_h7.1, cs_h7.2] at h
    rw [h, cos_flip (7/2:ℝ) x, sin_flip (7/2:ℝ) x]; ring
  have hcxl : (-176776695861/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-471396734543/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-881921266621/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-88388347351/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (5105088062083/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (10504700435441/1000000000000:ℝ) := by nlinarith
  have hp1 : (8448913500669/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (4346316137973/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-7666217267073/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1194856801977/100000000000:ℝ) := by nlinarith
  have hN : (5620730618163/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (219697462476709/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (5620730618163/500000000000:ℝ) (219697462476709/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (5236311191/2000000000000:ℝ) ≤ ((5620730618163/500000000000:ℝ)/(219697462476709/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_613 (x : ℝ) (h₁ : (13/4:ℝ) ≤ x) (h₂ : x ≤ (219/64:ℝ)) : (23861384437/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/500000000:ℝ) ≤ Real.pi * ((7/2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((7/2:ℝ) - x) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * ((7/2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((7/2:ℝ) - x)) ≤ (60626953467/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/500000000:ℝ) + taylorErr ≤ (60626953467/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (242980177581/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((7/2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (242980177581/1000000000000:ℝ) ≤ taylorSin (122718463/500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((7/2:ℝ) - x)) ≤ (176776695861/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/5000000000:ℝ) + taylorErr ≤ (176776695861/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((7/2:ℝ) - x)) := by
    have h := (trig_shift (7/2:ℝ) (x - (7/2:ℝ))).1
    rw [show (7/2:ℝ) + (x - (7/2:ℝ)) = x by ring, cs_h7.1, cs_h7.2] at h
    rw [h, cos_flip (7/2:ℝ) x, sin_flip (7/2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((7/2:ℝ) - x)) := by
    have h := (trig_shift (7/2:ℝ) (x - (7/2:ℝ))).2
    rw [show (7/2:ℝ) + (x - (7/2:ℝ)) = x by ring, cs_h7.1, cs_h7.2] at h
    rw [h, cos_flip (7/2:ℝ) x, sin_flip (7/2:ℝ) x]; ring
  have hcxl : (-176776695861/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-242980177581/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-60626953467/62500000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-88388347351/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (5105088062083/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (10750137361503/1000000000000:ℝ) := by nlinarith
  have hp1 : (8448913500669/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (4447865580449/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-3451654906539/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1194856801977/100000000000:ℝ) := by nlinarith
  have hN : (5620730618163/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (115065453291183/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (5620730618163/500000000000:ℝ) (115065453291183/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (23861384437/10000000000000:ℝ) ≤ ((5620730618163/500000000000:ℝ)/(115065453291183/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_614 (x : ℝ) (h₁ : (105/32:ℝ) ≤ x) (h₂ : x ≤ (841/256:ℝ)) : (175265383/50000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (3374757733/5000000000:ℝ) ≤ Real.pi * ((7/2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((7/2:ℝ) - x) ≤ (687223393/1000000000:ℝ) := by nlinarith
  have hc1 : (38650522553/50000000000:ℝ) ≤ Real.cos (Real.pi * ((7/2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (38650522553/50000000000:ℝ) ≤ taylorCos (687223393/1000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((7/2:ℝ) - x)) ≤ (780737230859/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (3374757733/5000000000:ℝ) + taylorErr ≤ (780737230859/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (24994379433/40000000000:ℝ) ≤ Real.sin (Real.pi * ((7/2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (24994379433/40000000000:ℝ) ≤ taylorSin (3374757733/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((7/2:ℝ) - x)) ≤ (317196643223/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (687223393/1000000000:ℝ) + taylorErr ≤ (317196643223/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((7/2:ℝ) - x)) := by
    have h := (trig_shift (7/2:ℝ) (x - (7/2:ℝ))).1
    rw [show (7/2:ℝ) + (x - (7/2:ℝ)) = x by ring, cs_h7.1, cs_h7.2] at h
    rw [h, cos_flip (7/2:ℝ) x, sin_flip (7/2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((7/2:ℝ) - x)) := by
    have h := (trig_shift (7/2:ℝ) (x - (7/2:ℝ))).2
    rw [show (7/2:ℝ) + (x - (7/2:ℝ)) = x by ring, cs_h7.1, cs_h7.2] at h
    rw [h, cos_flip (7/2:ℝ) x, sin_flip (7/2:ℝ) x]; ring
  have hcxl : (-317196643223/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-24994379433/40000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-780737230859/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-38650522553/50000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (10308350894591/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2064124548179/200000000000:ℝ) := by nlinarith
  have hp1 : (17060306107121/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1067538514029/62500000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-6667736506227/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-13187794919087/1000000000000:ℝ) := by nlinarith
  have hN : (12553401632641/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (212030507519759/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (12553401632641/1000000000000:ℝ) (212030507519759/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (175265383/50000000000:ℝ) ≤ ((12553401632641/1000000000000:ℝ)/(212030507519759/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_615 (x : ℝ) (h₁ : (841/256:ℝ) ≤ x) (h₂ : x ≤ (421/128:ℝ)) : (17882663363/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (6626797003/10000000000:ℝ) ≤ Real.pi * ((7/2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((7/2:ℝ) - x) ≤ (6749515467/10000000000:ℝ) := by nlinarith
  have hc1 : (24398038321/31250000000:ℝ) ≤ Real.cos (Real.pi * ((7/2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (24398038321/31250000000:ℝ) ≤ taylorCos (6749515467/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((7/2:ℝ) - x)) ≤ (157669285983/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (6626797003/10000000000:ℝ) + taylorErr ≤ (157669285983/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (123046317653/200000000000:ℝ) ≤ Real.sin (Real.pi * ((7/2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (123046317653/200000000000:ℝ) ≤ taylorSin (6626797003/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((7/2:ℝ) - x)) ≤ (624859490427/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (6749515467/10000000000:ℝ) + taylorErr ≤ (624859490427/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((7/2:ℝ) - x)) := by
    have h := (trig_shift (7/2:ℝ) (x - (7/2:ℝ))).1
    rw [show (7/2:ℝ) + (x - (7/2:ℝ)) = x by ring, cs_h7.1, cs_h7.2] at h
    rw [h, cos_flip (7/2:ℝ) x, sin_flip (7/2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((7/2:ℝ) - x)) := by
    have h := (trig_shift (7/2:ℝ) (x - (7/2:ℝ))).2
    rw [show (7/2:ℝ) + (x - (7/2:ℝ)) = x by ring, cs_h7.1, cs_h7.2] at h
    rw [h, cos_flip (7/2:ℝ) x, sin_flip (7/2:ℝ) x]; ring
  have hcxl : (-624859490427/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-123046317653/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-157669285983/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-24398038321/31250000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (5160311370447/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (5166447293599/500000000000:ℝ) := by nlinarith
  have hp1 : (1067538499709/62500000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (17100926112959/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-842590878087/62500000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-6667736377611/500000000000:ℝ) := by nlinarith
  have hN : (2542122652959/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (53134355275073/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2542122652959/200000000000:ℝ) (53134355275073/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (17882663363/5000000000000:ℝ) ≤ ((2542122652959/200000000000:ℝ)/(53134355275073/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_616 (x : ℝ) (h₁ : (421/128:ℝ) ≤ x) (h₂ : x ≤ (211/64:ℝ)) : (9074663383/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (6381360077/10000000000:ℝ) ≤ Real.pi * ((7/2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((7/2:ℝ) - x) ≤ (1656699251/2500000000:ℝ) := by nlinarith
  have hc1 : (788346425329/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((7/2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (788346425329/1000000000000:ℝ) ≤ taylorCos (1656699251/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((7/2:ℝ) - x)) ≤ (803207533769/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (6381360077/10000000000:ℝ) + taylorErr ≤ (803207533769/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (595699302181/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((7/2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (595699302181/1000000000000:ℝ) ≤ taylorSin (6381360077/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((7/2:ℝ) - x)) ≤ (153807898217/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1656699251/2500000000:ℝ) + taylorErr ≤ (153807898217/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((7/2:ℝ) - x)) := by
    have h := (trig_shift (7/2:ℝ) (x - (7/2:ℝ))).1
    rw [show (7/2:ℝ) + (x - (7/2:ℝ)) = x by ring, cs_h7.1, cs_h7.2] at h
    rw [h, cos_flip (7/2:ℝ) x, sin_flip (7/2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((7/2:ℝ) - x)) := by
    have h := (trig_shift (7/2:ℝ) (x - (7/2:ℝ))).2
    rw [show (7/2:ℝ) + (x - (7/2:ℝ)) = x by ring, cs_h7.1, cs_h7.2] at h
    rw [h, cos_flip (7/2:ℝ) x, sin_flip (7/2:ℝ) x]; ring
  have hcxl : (-153807898217/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-595699302181/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-803207533769/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-788346425329/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (10332894587197/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2589359569951/250000000000:ℝ) := by nlinarith
  have hp1 : (8550462941783/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (17141545889949/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2753643759851/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-107851630321/8000000000:ℝ) := by nlinarith
  have hN : (12866222197257/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (213553055439899/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (12866222197257/1000000000000:ℝ) (213553055439899/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (9074663383/2500000000000:ℝ) ≤ ((12866222197257/1000000000000:ℝ)/(213553055439899/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_617 (x : ℝ) (h₁ : (211/64:ℝ) ≤ x) (h₂ : x ≤ (53/16:ℝ)) : (37331393477/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (235619449/400000000:ℝ) ≤ Real.pi * ((7/2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((7/2:ℝ) - x) ≤ (3190680039/5000000000:ℝ) := by nlinarith
  have hc1 : (160641505837/200000000000:ℝ) ≤ Real.cos (Real.pi * ((7/2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (160641505837/200000000000:ℝ) ≤ taylorCos (3190680039/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((7/2:ℝ) - x)) ≤ (207867403647/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (235619449/400000000:ℝ) + taylorErr ≤ (207867403647/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (555570230717/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((7/2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (555570230717/1000000000000:ℝ) ≤ taylorSin (235619449/400000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((7/2:ℝ) - x)) ≤ (297849653393/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3190680039/5000000000:ℝ) + taylorErr ≤ (297849653393/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((7/2:ℝ) - x)) := by
    have h := (trig_shift (7/2:ℝ) (x - (7/2:ℝ))).1
    rw [show (7/2:ℝ) + (x - (7/2:ℝ)) = x by ring, cs_h7.1, cs_h7.2] at h
    rw [h, cos_flip (7/2:ℝ) x, sin_flip (7/2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((7/2:ℝ) - x)) := by
    have h := (trig_shift (7/2:ℝ) (x - (7/2:ℝ))).2
    rw [show (7/2:ℝ) + (x - (7/2:ℝ)) = x by ring, cs_h7.1, cs_h7.2] at h
    rw [h, cos_flip (7/2:ℝ) x, sin_flip (7/2:ℝ) x]; ring
  have hcxl : (-297849653393/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-555570230717/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-207867403647/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-160641505837/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (10357438279803/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (10406525665017/1000000000000:ℝ) := by nlinarith
  have hp1 : (4285386415003/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (17222785443931/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-7160111387599/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1376821853599/100000000000:ℝ) := by nlinarith
  have hN : (3293129807301/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (53897888208329/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3293129807301/250000000000:ℝ) (53897888208329/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (37331393477/10000000000000:ℝ) ≤ ((3293129807301/250000000000:ℝ)/(53897888208329/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_618 (x : ℝ) (h₁ : (53/16:ℝ) ≤ x) (h₂ : x ≤ (27/8:ℝ)) : (7562713/2000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/312500000:ℝ) ≤ Real.pi * ((7/2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((7/2:ℝ) - x) ≤ (2945243113/5000000000:ℝ) := by nlinarith
  have hc1 : (103933701251/125000000000:ℝ) ≤ Real.cos (Real.pi * ((7/2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (103933701251/125000000000:ℝ) ≤ taylorCos (2945243113/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((7/2:ℝ) - x)) ≤ (923879534811/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/312500000:ℝ) + taylorErr ≤ (923879534811/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (95670857503/250000000000:ℝ) ≤ Real.sin (Real.pi * ((7/2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (95670857503/250000000000:ℝ) ≤ taylorSin (122718463/312500000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((7/2:ℝ) - x)) ≤ (22222809413/40000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2945243113/5000000000:ℝ) + taylorErr ≤ (22222809413/40000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((7/2:ℝ) - x)) := by
    have h := (trig_shift (7/2:ℝ) (x - (7/2:ℝ))).1
    rw [show (7/2:ℝ) + (x - (7/2:ℝ)) = x by ring, cs_h7.1, cs_h7.2] at h
    rw [h, cos_flip (7/2:ℝ) x, sin_flip (7/2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((7/2:ℝ) - x)) := by
    have h := (trig_shift (7/2:ℝ) (x - (7/2:ℝ))).2
    rw [show (7/2:ℝ) + (x - (7/2:ℝ)) = x by ring, cs_h7.1, cs_h7.2] at h
    rw [h, cos_flip (7/2:ℝ) x, sin_flip (7/2:ℝ) x]; ring
  have hcxl : (-22222809413/40000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-95670857503/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-923879534811/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-103933701251/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1300815708127/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (5301437602933/500000000000:ℝ) := by nlinarith
  have hp1 : (2152848151613/125000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (8773871829927/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-16212001249449/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-447506953257/31250000000:ℝ) := by nlinarith
  have hN : (13764652268899/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (218595630139/976562500:ℝ) := by nlinarith
  have hfin := wfun_ge x (13764652268899/1000000000000:ℝ) (218595630139/976562500:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (7562713/2000000000:ℝ) ≤ ((13764652268899/1000000000000:ℝ)/(218595630139/976562500:ℝ))^2 := by norm_num
  linarith

theorem wc_619 (x : ℝ) (h₁ : (27/8:ℝ) ≤ x) (h₂ : x ≤ (7/2:ℝ)) : (43210796373/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * ((7/2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((7/2:ℝ) - x) ≤ (3926990817/10000000000:ℝ) := by nlinarith
  have hc1 : (923879530249/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((7/2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (923879530249/1000000000000:ℝ) ≤ taylorCos (3926990817/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((7/2:ℝ) - x)) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * ((7/2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((7/2:ℝ) - x)) ≤ (95670858657/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/10000000000:ℝ) + taylorErr ≤ (95670858657/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((7/2:ℝ) - x)) := by
    have h := (trig_shift (7/2:ℝ) (x - (7/2:ℝ))).1
    rw [show (7/2:ℝ) + (x - (7/2:ℝ)) = x by ring, cs_h7.1, cs_h7.2] at h
    rw [h, cos_flip (7/2:ℝ) x, sin_flip (7/2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((7/2:ℝ) - x)) := by
    have h := (trig_shift (7/2:ℝ) (x - (7/2:ℝ))).2
    rw [show (7/2:ℝ) + (x - (7/2:ℝ)) = x by ring, cs_h7.1, cs_h7.2] at h
    rw [h, cos_flip (7/2:ℝ) x, sin_flip (7/2:ℝ) x]; ring
  have hcxl : (-95670858657/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (1131/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-500000001131/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-923879530249/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (2120575041173/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2199114857513/200000000000:ℝ) := by nlinarith
  have hp1 : (17547743424467/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (18197660091701/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-3639532026573/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-8106000475963/500000000000:ℝ) := by nlinarith
  have hN : (7914658758649/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (120402653913361/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (7914658758649/500000000000:ℝ) (120402653913361/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (43210796373/10000000000000:ℝ) ≤ ((7914658758649/500000000000:ℝ)/(120402653913361/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_620 (x : ℝ) (h₁ : (7/2:ℝ) ≤ x) (h₂ : x ≤ (29/8:ℝ)) : (1058437871/250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * (x - (7/2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (7/2:ℝ)) ≤ (3926990817/10000000000:ℝ) := by nlinarith
  have hc1 : (923879530249/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (7/2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (923879530249/1000000000000:ℝ) ≤ taylorCos (3926990817/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (7/2:ℝ))) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (7/2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (7/2:ℝ))) ≤ (95670858657/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/10000000000:ℝ) + taylorErr ≤ (95670858657/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (7/2:ℝ))) := by
    have h := (trig_shift (7/2:ℝ) (x - (7/2:ℝ))).1
    rw [show (7/2:ℝ) + (x - (7/2:ℝ)) = x by ring, cs_h7.1, cs_h7.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (7/2:ℝ))) := by
    have h := (trig_shift (7/2:ℝ) (x - (7/2:ℝ))).2
    rw [show (7/2:ℝ) + (x - (7/2:ℝ)) = x by ring, cs_h7.1, cs_h7.2] at h
    rw [h]; ring
  have hcxl : (-1131/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (95670858657/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-500000001131/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-923879530249/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (2748893571891/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (711767085579/62500000000:ℝ) := by nlinarith
  have hp1 : (4549414961899/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (18847576523547/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-18847576566181/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-4203111357907/250000000000:ℝ) := by nlinarith
  have hN : (8406222714683/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (4037274072909/15625000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (8406222714683/500000000000:ℝ) (4037274072909/15625000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1058437871/250000000000:ℝ) ≤ ((8406222714683/500000000000:ℝ)/(4037274072909/15625000000:ℝ))^2 := by norm_num
  linarith

theorem wc_621 (x : ℝ) (h₁ : (29/8:ℝ) ≤ x) (h₂ : x ≤ (59/16:ℝ)) : (9010606921/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/312500000:ℝ) ≤ Real.pi * (x - (7/2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (7/2:ℝ)) ≤ (2945243113/5000000000:ℝ) := by nlinarith
  have hc1 : (103933701251/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (7/2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (103933701251/125000000000:ℝ) ≤ taylorCos (2945243113/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (7/2:ℝ))) ≤ (923879534811/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/312500000:ℝ) + taylorErr ≤ (923879534811/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (95670857503/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (7/2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (95670857503/250000000000:ℝ) ≤ taylorSin (122718463/312500000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (7/2:ℝ))) ≤ (22222809413/40000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2945243113/5000000000:ℝ) + taylorErr ≤ (22222809413/40000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (7/2:ℝ))) := by
    have h := (trig_shift (7/2:ℝ) (x - (7/2:ℝ))).1
    rw [show (7/2:ℝ) + (x - (7/2:ℝ)) = x by ring, cs_h7.1, cs_h7.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (7/2:ℝ))) := by
    have h := (trig_shift (7/2:ℝ) (x - (7/2:ℝ))).2
    rw [show (7/2:ℝ) + (x - (7/2:ℝ)) = x by ring, cs_h7.1, cs_h7.2] at h
    rw [h]; ring
  have hcxl : (95670857503/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (22222809413/40000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-923879534811/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-103933701251/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (11388273369263/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (11584622910113/1000000000000:ℝ) := by nlinarith
  have hp1 : (753903050829/40000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1917253473947/100000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-14170489981/800000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-3134237378283/200000000000:ℝ) := by nlinarith
  have hN : (16053870321427/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (26740697593903/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (16053870321427/1000000000000:ℝ) (26740697593903/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (9010606921/2500000000000:ℝ) ≤ ((16053870321427/1000000000000:ℝ)/(26740697593903/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_622 (x : ℝ) (h₁ : (59/16:ℝ) ≤ x) (h₂ : x ≤ (237/64:ℝ)) : (35001008619/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (235619449/400000000:ℝ) ≤ Real.pi * (x - (7/2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (7/2:ℝ)) ≤ (3190680039/5000000000:ℝ) := by nlinarith
  have hc1 : (160641505837/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (7/2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (160641505837/200000000000:ℝ) ≤ taylorCos (3190680039/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (7/2:ℝ))) ≤ (207867403647/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (235619449/400000000:ℝ) + taylorErr ≤ (207867403647/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (555570230717/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (7/2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (555570230717/1000000000000:ℝ) ≤ taylorSin (235619449/400000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (7/2:ℝ))) ≤ (297849653393/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3190680039/5000000000:ℝ) + taylorErr ≤ (297849653393/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (7/2:ℝ))) := by
    have h := (trig_shift (7/2:ℝ) (x - (7/2:ℝ))).1
    rw [show (7/2:ℝ) + (x - (7/2:ℝ)) = x by ring, cs_h7.1, cs_h7.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (7/2:ℝ))) := by
    have h := (trig_shift (7/2:ℝ) (x - (7/2:ℝ))).2
    rw [show (7/2:ℝ) + (x - (7/2:ℝ)) = x by ring, cs_h7.1, cs_h7.2] at h
    rw [h]; ring
  have hcxl : (555570230717/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (297849653393/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-207867403647/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-160641505837/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (362019465941/31250000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (465348411813/40000000000:ℝ) := by nlinarith
  have hp1 : (19172534482289/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (385075485869/20000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-800446414557/50000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-15399524049733/1000000000000:ℝ) := by nlinarith
  have hN : (319101885609/20000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (134843215235551/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (319101885609/20000000000:ℝ) (134843215235551/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (35001008619/10000000000000:ℝ) ≤ ((319101885609/20000000000:ℝ)/(134843215235551/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_623 (x : ℝ) (h₁ : (237/64:ℝ) ≤ x) (h₂ : x ≤ (15/4:ℝ)) : (26396659657/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (6381360077/10000000000:ℝ) ≤ Real.pi * (x - (7/2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (7/2:ℝ)) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (7/2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (7/2:ℝ))) ≤ (803207533769/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (6381360077/10000000000:ℝ) + taylorErr ≤ (803207533769/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (595699302181/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (7/2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (595699302181/1000000000000:ℝ) ≤ taylorSin (6381360077/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (7/2:ℝ))) ≤ (176776695861/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/5000000000:ℝ) + taylorErr ≤ (176776695861/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (7/2:ℝ))) := by
    have h := (trig_shift (7/2:ℝ) (x - (7/2:ℝ))).1
    rw [show (7/2:ℝ) + (x - (7/2:ℝ)) = x by ring, cs_h7.1, cs_h7.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (7/2:ℝ))) := by
    have h := (trig_shift (7/2:ℝ) (x - (7/2:ℝ))).2
    rw [show (7/2:ℝ) + (x - (7/2:ℝ)) = x by ring, cs_h7.1, cs_h7.2] at h
    rw [h]; ring
  have hcxl : (595699302181/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (176776695861/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-803207533769/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-88388347351/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (2908427573831/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (5890486225481/500000000000:ℝ) := by nlinarith
  have hp1 : (19253774035179/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (19497492955393/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-783026661569/50000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1701809267239/125000000000:ℝ) := by nlinarith
  have hN : (14210173440093/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (69145655945163/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (14210173440093/1000000000000:ℝ) (69145655945163/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (26396659657/10000000000000:ℝ) ≤ ((14210173440093/1000000000000:ℝ)/(69145655945163/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_624 (x : ℝ) (h₁ : (15/4:ℝ) ≤ x) (h₂ : x ≤ (19639/5120:ℝ)) : (6366839399/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (516031137/1000000000:ℝ) ≤ Real.pi * ((4:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((4:ℝ) - x) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((4:ℝ) - x)) ≤ (217446097769/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (516031137/1000000000:ℝ) + taylorErr ≤ (217446097769/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (493431975799/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (493431975799/1000000000000:ℝ) ≤ taylorSin (516031137/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((4:ℝ) - x)) ≤ (176776695861/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/5000000000:ℝ) + taylorErr ≤ (176776695861/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hcxl : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (217446097769/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-176776695861/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-493431975799/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (11780972450961/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2410067895463/200000000000:ℝ) := by nlinarith
  have hp1 : (4874373173463/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (19943295007863/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2820407836857/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-9620686343053/1000000000000:ℝ) := by nlinarith
  have hN : (10327793121861/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (289421363037073/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (10327793121861/1000000000000:ℝ) (289421363037073/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (6366839399/5000000000000:ℝ) ≤ ((10327793121861/1000000000000:ℝ)/(289421363037073/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_625 (x : ℝ) (h₁ : (19639/5120:ℝ) ≤ x) (h₂ : x ≤ (10159/2560:ℝ)) : (8453897/100000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (19880391/200000000:ℝ) ≤ Real.pi * ((4:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((4:ℝ) - x) ≤ (5160311371/10000000000:ℝ) := by nlinarith
  have hc1 : (869784386503/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (869784386503/1000000000000:ℝ) ≤ taylorCos (5160311371/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((4:ℝ) - x)) ≤ (995063694477/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (19880391/200000000:ℝ) + taylorErr ≤ (995063694477/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (99238339301/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (99238339301/1000000000000:ℝ) ≤ taylorSin (19880391/200000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((4:ℝ) - x)) ≤ (493431980411/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (5160311371/10000000000:ℝ) + taylorErr ≤ (493431980411/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hcxl : (869784386503/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (995063694477/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-493431980411/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-99238339301/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6025169738657/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2493393731861/200000000000:ℝ) := by nlinarith
  have hp1 : (19943294740343/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (825312628891/40000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-5090445561649/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-989569725111/500000000000:ℝ) := by nlinarith
  have hN : (113956953469/40000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (309850615104187/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (113956953469/40000000000:ℝ) (309850615104187/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (8453897/100000000000:ℝ) ≤ ((113956953469/40000000000:ℝ)/(309850615104187/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_626 (x : ℝ) (h₁ : (999/256:ℝ) ≤ x) (h₂ : x ≤ (4:ℝ)) : (91689533/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * ((4:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((4:ℝ) - x) ≤ (383495197/1250000000:ℝ) := by nlinarith
  have hc1 : (190661207617/200000000000:ℝ) ≤ Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (190661207617/200000000000:ℝ) ≤ taylorCos (383495197/1250000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((4:ℝ) - x)) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((4:ℝ) - x)) ≤ (302005951603/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (383495197/1250000000:ℝ) + taylorErr ≤ (302005951603/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hcxl : (190661207617/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (500000001131/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-302005951603/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1131/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6129787228391/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (314159265359/25000000000:ℝ) := by nlinarith
  have hp1 : (20289578334541/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10398662909543/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-6280916174791/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (11761/250000000000:ℝ) := by nlinarith
  have hN : (953305991041/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (157413670417451/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (953305991041/1000000000000:ℝ) (157413670417451/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (91689533/10000000000000:ℝ) ≤ ((953305991041/1000000000000:ℝ)/(157413670417451/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_627 (x : ℝ) (h₁ : (63/16:ℝ) ≤ x) (h₂ : x ≤ (509/128:ℝ)) : (319416431/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (368155389/5000000000:ℝ) ≤ Real.pi * ((4:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((4:ℝ) - x) ≤ (1963495409/10000000000:ℝ) := by nlinarith
  have hc1 : (980785278131/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (980785278131/1000000000000:ℝ) ≤ taylorCos (1963495409/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((4:ℝ) - x)) ≤ (498645229471/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (368155389/5000000000:ℝ) + taylorErr ≤ (498645229471/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (73564561319/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (73564561319/1000000000000:ℝ) ≤ taylorSin (368155389/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((4:ℝ) - x)) ≤ (24386290541/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1963495409/10000000000:ℝ) + taylorErr ≤ (24386290541/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hcxl : (980785278131/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (498645229471/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-24386290541/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-73564561319/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12370021073509/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12492739536541/1000000000000:ℝ) := by nlinarith
  have hp1 : (4094473465709/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10337733244057/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-4033583462799/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-301208144337/200000000000:ℝ) := by nlinarith
  have hN : (310853249977/125000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (31113708225571/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (310853249977/125000000000:ℝ) (31113708225571/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (319416431/5000000000000:ℝ) ≤ ((310853249977/125000000000:ℝ)/(31113708225571/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_628 (x : ℝ) (h₁ : (63/16:ℝ) ≤ x) (h₂ : x ≤ (1023/256:ℝ)) : (38435113/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/10000000000:ℝ) ≤ Real.pi * ((4:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((4:ℝ) - x) ≤ (1963495409/10000000000:ℝ) := by nlinarith
  have hc1 : (980785278131/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (980785278131/1000000000000:ℝ) ≤ taylorCos (1963495409/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((4:ℝ) - x)) ≤ (999924704101/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/10000000000:ℝ) + taylorErr ≤ (999924704101/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (613576801/50000000000:ℝ) ≤ Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (613576801/50000000000:ℝ) ≤ taylorSin (122718463/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((4:ℝ) - x)) ≤ (24386290541/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1963495409/10000000000:ℝ) + taylorErr ≤ (24386290541/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hcxl : (980785278131/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999924704101/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-24386290541/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-613576801/50000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12370021073509/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12554098768057/1000000000000:ℝ) := by nlinarith
  have hp1 : (4094473465709/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (20777015930591/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1013348694117/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-125613696543/500000000000:ℝ) := by nlinarith
  have hN : (1232012671217/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (314210791756261/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1232012671217/1000000000000:ℝ) (314210791756261/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (38435113/2500000000000:ℝ) ≤ ((1232012671217/1000000000000:ℝ)/(314210791756261/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_629 (x : ℝ) (h₁ : (1009/256:ℝ) ≤ x) (h₂ : x ≤ (4087/1024:ℝ)) : (122092393/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (276116541/10000000000:ℝ) ≤ Real.pi * ((4:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((4:ℝ) - x) ≤ (920388473/5000000000:ℝ) := by nlinarith
  have hc1 : (983105485159/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (983105485159/1000000000000:ℝ) ≤ taylorCos (920388473/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((4:ℝ) - x)) ≤ (24990470619/25000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (276116541/10000000000:ℝ) + taylorErr ≤ (24990470619/25000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (5521628687/200000000000:ℝ) ≤ Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (5521628687/200000000000:ℝ) ≤ taylorSin (276116541/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((4:ℝ) - x)) ≤ (18303989027/100000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (920388473/5000000000:ℝ) + taylorErr ≤ (18303989027/100000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hcxl : (983105485159/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (24990470619/25000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-18303989027/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-5521628687/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3095573229953/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6269379480089/500000000000:ℝ) := by nlinarith
  have hp1 : (40024760189/1953125000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5187907142493/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-949593954093/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-565764771967/1000000000000:ℝ) := by nlinarith
  have hN : (774435128563/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (313440952522889/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (774435128563/500000000000:ℝ) (313440952522889/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (122092393/5000000000000:ℝ) ≤ ((774435128563/500000000000:ℝ)/(313440952522889/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_630 (x : ℝ) (h₁ : (1009/256:ℝ) ≤ x) (h₂ : x ≤ (4:ℝ)) : (48755691/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * ((4:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((4:ℝ) - x) ≤ (920388473/5000000000:ℝ) := by nlinarith
  have hc1 : (983105485159/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (983105485159/1000000000000:ℝ) ≤ taylorCos (920388473/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((4:ℝ) - x)) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((4:ℝ) - x)) ≤ (18303989027/100000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (920388473/5000000000:ℝ) + taylorErr ≤ (18303989027/100000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hcxl : (983105485159/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (500000001131/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-18303989027/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1131/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3095573229953/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (314159265359/25000000000:ℝ) := by nlinarith
  have hp1 : (40024760189/1953125000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10398662909543/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-761348047167/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (11761/250000000000:ℝ) := by nlinarith
  have hN : (196621087623/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (157413670417451/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (196621087623/200000000000:ℝ) (157413670417451/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (48755691/5000000000000:ℝ) ≤ ((196621087623/200000000000:ℝ)/(157413670417451/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_631 (x : ℝ) (h₁ : (1013/256:ℝ) ≤ x) (h₂ : x ≤ (2041/512:ℝ)) : (71867913/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (21475731/500000000:ℝ) ≤ Real.pi * ((4:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((4:ℝ) - x) ≤ (674951547/5000000000:ℝ) := by nlinarith
  have hc1 : (990902633157/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (990902633157/1000000000000:ℝ) ≤ taylorCos (674951547/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((4:ℝ) - x)) ≤ (999077730017/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (21475731/500000000:ℝ) + taylorErr ≤ (999077730017/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (10734563653/250000000000:ℝ) ≤ Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (10734563653/250000000000:ℝ) ≤ taylorSin (21475731/500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((4:ℝ) - x)) ≤ (26916142167/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (674951547/5000000000:ℝ) + taylorErr ≤ (26916142167/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hcxl : (990902633157/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999077730017/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-26916142167/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-10734563653/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (497255212201/40000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12523419152299/1000000000000:ℝ) := by nlinarith
  have hp1 : (1028695838483/50000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (20726241209353/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2789352274893/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-883408076621/1000000000000:ℝ) := by nlinarith
  have hN : (937155354889/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (312672054528339/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (937155354889/500000000000:ℝ) (312672054528339/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (71867913/2000000000000:ℝ) ≤ ((937155354889/500000000000:ℝ)/(312672054528339/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_632 (x : ℝ) (h₁ : (1013/256:ℝ) ≤ x) (h₂ : x ≤ (1023/256:ℝ)) : (31317919/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/10000000000:ℝ) ≤ Real.pi * ((4:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((4:ℝ) - x) ≤ (674951547/5000000000:ℝ) := by nlinarith
  have hc1 : (990902633157/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (990902633157/1000000000000:ℝ) ≤ taylorCos (674951547/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((4:ℝ) - x)) ≤ (999924704101/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/10000000000:ℝ) + taylorErr ≤ (999924704101/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (613576801/50000000000:ℝ) ≤ Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (613576801/50000000000:ℝ) ≤ taylorSin (122718463/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((4:ℝ) - x)) ≤ (26916142167/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (674951547/5000000000:ℝ) + taylorErr ≤ (26916142167/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hcxl : (990902633157/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999924704101/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-26916142167/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-613576801/50000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (497255212201/40000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12554098768057/1000000000000:ℝ) := by nlinarith
  have hp1 : (1028695838483/50000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (20777015930591/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-279618557297/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-252473560711/1000000000000:ℝ) := by nlinarith
  have hN : (310844048467/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (314210791756261/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (310844048467/250000000000:ℝ) (314210791756261/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (31317919/2000000000000:ℝ) ≤ ((310844048467/250000000000:ℝ)/(314210791756261/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_633 (x : ℝ) (h₁ : (507/128:ℝ) ≤ x) (h₂ : x ≤ (8183/2048:ℝ)) : (82600037/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (13805827/1000000000:ℝ) ≤ Real.pi * ((4:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((4:ℝ) - x) ≤ (1227184631/10000000000:ℝ) := by nlinarith
  have hc1 : (124059941541/125000000000:ℝ) ≤ Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (124059941541/125000000000:ℝ) ≤ taylorCos (1227184631/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((4:ℝ) - x)) ≤ (499952351673/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (13805827/1000000000:ℝ) + taylorErr ≤ (499952351673/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (552215447/40000000000:ℝ) ≤ Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (552215447/40000000000:ℝ) ≤ taylorSin (13805827/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((4:ℝ) - x)) ≤ (12241067753/100000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1227184631/10000000000:ℝ) + taylorErr ≤ (12241067753/100000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hcxl : (124059941541/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (499952351673/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-12241067753/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-552215447/40000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (388864129729/31250000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12552564787269/1000000000000:ℝ) := by nlinarith
  have hp1 : (10297113328941/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (20774477194529/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1271508914357/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-284311251987/1000000000000:ℝ) := by nlinarith
  have hN : (255358156863/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (78533441369293/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (255358156863/200000000000:ℝ) (78533441369293/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (82600037/5000000000000:ℝ) ≤ ((255358156863/200000000000:ℝ)/(78533441369293/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_634 (x : ℝ) (h₁ : (507/128:ℝ) ≤ x) (h₂ : x ≤ (4:ℝ)) : (99379817/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * ((4:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((4:ℝ) - x) ≤ (1227184631/10000000000:ℝ) := by nlinarith
  have hc1 : (124059941541/125000000000:ℝ) ≤ Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (124059941541/125000000000:ℝ) ≤ taylorCos (1227184631/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((4:ℝ) - x)) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((4:ℝ) - x)) ≤ (12241067753/100000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1227184631/10000000000:ℝ) + taylorErr ≤ (12241067753/100000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hcxl : (124059941541/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (500000001131/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-12241067753/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1131/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (388864129729/31250000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (314159265359/25000000000:ℝ) := by nlinarith
  have hp1 : (10297113328941/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10398662909543/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2545814744327/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (11761/250000000000:ℝ) := by nlinarith
  have hN : (248119871321/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (157413670417451/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (248119871321/250000000000:ℝ) (157413670417451/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (99379817/10000000000000:ℝ) ≤ ((248119871321/250000000000:ℝ)/(157413670417451/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_635 (x : ℝ) (h₁ : (2031/512:ℝ) ≤ x) (h₂ : x ≤ (2041/512:ℝ)) : (11299473/312500000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (21475731/500000000:ℝ) ≤ Real.pi * ((4:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((4:ℝ) - x) ≤ (130388367/1250000000:ℝ) := by nlinarith
  have hc1 : (99456456847/100000000000:ℝ) ≤ Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (99456456847/100000000000:ℝ) ≤ taylorCos (130388367/1250000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((4:ℝ) - x)) ≤ (999077730017/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (21475731/500000000:ℝ) + taylorErr ≤ (999077730017/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (10734563653/250000000000:ℝ) ≤ Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (10734563653/250000000000:ℝ) ≤ taylorSin (21475731/500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((4:ℝ) - x)) ≤ (52060818079/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (130388367/1250000000:ℝ) + taylorErr ≤ (52060818079/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hcxl : (99456456847/100000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999077730017/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-52060818079/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-10734563653/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6231029960391/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12523419152299/1000000000000:ℝ) := by nlinarith
  have hp1 : (2578086436277/125000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (20726241209353/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-539512536531/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1771176509/2000000000:ℝ) := by nlinarith
  have hN : (188015282297/100000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (312672054528339/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (188015282297/100000000000:ℝ) (312672054528339/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (11299473/312500000000:ℝ) ≤ ((188015282297/100000000000:ℝ)/(312672054528339/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_636 (x : ℝ) (h₁ : (2031/512:ℝ) ≤ x) (h₂ : x ≤ (1023/256:ℝ)) : (157670757/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/10000000000:ℝ) ≤ Real.pi * ((4:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((4:ℝ) - x) ≤ (130388367/1250000000:ℝ) := by nlinarith
  have hc1 : (99456456847/100000000000:ℝ) ≤ Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (99456456847/100000000000:ℝ) ≤ taylorCos (130388367/1250000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((4:ℝ) - x)) ≤ (999924704101/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/10000000000:ℝ) + taylorErr ≤ (999924704101/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (613576801/50000000000:ℝ) ≤ Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (613576801/50000000000:ℝ) ≤ taylorSin (122718463/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((4:ℝ) - x)) ≤ (52060818079/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (130388367/1250000000:ℝ) + taylorErr ≤ (52060818079/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hcxl : (99456456847/100000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999924704101/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-52060818079/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-613576801/50000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6231029960391/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12554098768057/1000000000000:ℝ) := by nlinarith
  have hp1 : (2578086436277/125000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (20777015930591/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1081668446587/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-253096644523/1000000000000:ℝ) := by nlinarith
  have hN : (1247661212993/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (314210791756261/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1247661212993/1000000000000:ℝ) (314210791756261/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (157670757/10000000000000:ℝ) ≤ ((1247661212993/1000000000000:ℝ)/(314210791756261/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_637 (x : ℝ) (h₁ : (4067/1024:ℝ) ≤ x) (h₂ : x ≤ (8185/2048:ℝ)) : (30026951/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (21475731/2000000000:ℝ) ≤ Real.pi * ((4:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((4:ℝ) - x) ≤ (889708857/10000000000:ℝ) := by nlinarith
  have hc1 : (996044698639/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (996044698639/1000000000000:ℝ) ≤ taylorCos (889708857/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((4:ℝ) - x)) ≤ (499971175969/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (21475731/2000000000:ℝ) + taylorErr ≤ (499971175969/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (1073765689/100000000000:ℝ) ≤ Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (1073765689/100000000000:ℝ) ≤ taylorSin (21475731/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((4:ℝ) - x)) ≤ (88853554847/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (889708857/10000000000:ℝ) + taylorErr ≤ (88853554847/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hcxl : (996044698639/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (499971175969/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-88853554847/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-1073765689/100000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12477399728661/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3138908187211/250000000000:ℝ) := by nlinarith
  have hp1 : (10325039425247/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5194888666663/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-184633730027/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-27716682681/125000000000:ℝ) := by nlinarith
  have hN : (1217778160087/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (39285978430961/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1217778160087/1000000000000:ℝ) (39285978430961/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (30026951/2000000000000:ℝ) ≤ ((1217778160087/1000000000000:ℝ)/(39285978430961/125000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_638 (x : ℝ) (h₁ : (4067/1024:ℝ) ≤ x) (h₂ : x ≤ (4:ℝ)) : (2502377/250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * ((4:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((4:ℝ) - x) ≤ (889708857/10000000000:ℝ) := by nlinarith
  have hc1 : (996044698639/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (996044698639/1000000000000:ℝ) ≤ taylorCos (889708857/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((4:ℝ) - x)) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((4:ℝ) - x)) ≤ (88853554847/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (889708857/10000000000:ℝ) + taylorErr ≤ (88853554847/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hcxl : (996044698639/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (500000001131/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-88853554847/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1131/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12477399728661/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (314159265359/25000000000:ℝ) := by nlinarith
  have hp1 : (10325039425247/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10398662909543/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-923958165169/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (11761/250000000000:ℝ) := by nlinarith
  have hN : (199208930319/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (157413670417451/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (199208930319/200000000000:ℝ) (157413670417451/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2502377/250000000000:ℝ) ≤ ((199208930319/200000000000:ℝ)/(157413670417451/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_639 (x : ℝ) (h₁ : (8143/2048:ℝ) ≤ x) (h₂ : x ≤ (16357/4096:ℝ)) : (103153789/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (103543703/5000000000:ℝ) ≤ Real.pi * ((4:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((4:ℝ) - x) ≤ (751650587/10000000000:ℝ) := by nlinarith
  have hc1 : (498588217233/500000000000:ℝ) ≤ Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (498588217233/500000000000:ℝ) ≤ taylorCos (751650587/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((4:ℝ) - x)) ≤ (999785583957/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (103543703/5000000000:ℝ) + taylorErr ≤ (999785583957/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (10353629103/500000000000:ℝ) ≤ Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (10353629103/500000000000:ℝ) ≤ taylorSin (103543703/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((4:ℝ) - x)) ≤ (75094303203/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (751650587/10000000000:ℝ) + taylorErr ≤ (75094303203/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hcxl : (498588217233/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999785583957/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-75094303203/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-10353629103/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1561400694469/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12545661873723/1000000000000:ℝ) := by nlinarith
  have hp1 : (4134585494949/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (83052211529/4000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-19489837357/12500000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-428079647093/1000000000000:ℝ) := by nlinarith
  have hN : (1425256081559/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (156893631849787/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1425256081559/1000000000000:ℝ) (156893631849787/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (103153789/5000000000000:ℝ) ≤ ((1425256081559/1000000000000:ℝ)/(156893631849787/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_640 (x : ℝ) (h₁ : (8143/2048:ℝ) ≤ x) (h₂ : x ≤ (4:ℝ)) : (100322671/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * ((4:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((4:ℝ) - x) ≤ (751650587/10000000000:ℝ) := by nlinarith
  have hc1 : (498588217233/500000000000:ℝ) ≤ Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (498588217233/500000000000:ℝ) ≤ taylorCos (751650587/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((4:ℝ) - x)) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((4:ℝ) - x)) ≤ (75094303203/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (751650587/10000000000:ℝ) + taylorErr ≤ (75094303203/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hcxl : (498588217233/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (500000001131/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-75094303203/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1131/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1561400694469/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (314159265359/25000000000:ℝ) := by nlinarith
  have hp1 : (4134585494949/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10398662909543/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1561760690871/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (11761/250000000000:ℝ) := by nlinarith
  have hN : (498588193711/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (157413670417451/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (498588193711/500000000000:ℝ) (157413670417451/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (100322671/10000000000000:ℝ) ≤ ((498588193711/500000000000:ℝ)/(157413670417451/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_641 (x : ℝ) (h₁ : (509/128:ℝ) ≤ x) (h₂ : x ≤ (4087/1024:ℝ)) : (250286237/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (276116541/10000000000:ℝ) ≤ Real.pi * ((4:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((4:ℝ) - x) ≤ (736310779/10000000000:ℝ) := by nlinarith
  have hc1 : (997290454411/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (997290454411/1000000000000:ℝ) ≤ taylorCos (736310779/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((4:ℝ) - x)) ≤ (24990470619/25000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (276116541/10000000000:ℝ) + taylorErr ≤ (24990470619/25000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (5521628687/200000000000:ℝ) ≤ Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (5521628687/200000000000:ℝ) ≤ taylorSin (276116541/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((4:ℝ) - x)) ≤ (73564565943/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (736310779/10000000000:ℝ) + taylorErr ≤ (73564565943/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hcxl : (997290454411/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (24990470619/25000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-73564565943/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-5521628687/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (624636976827/50000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6269379480089/500000000000:ℝ) := by nlinarith
  have hp1 : (20675466210773/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5187907142493/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1526584548361/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-142702809183/250000000000:ℝ) := by nlinarith
  have hN : (1568101691143/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (313440952522889/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1568101691143/1000000000000:ℝ) (313440952522889/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (250286237/10000000000000:ℝ) ≤ ((1568101691143/1000000000000:ℝ)/(313440952522889/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_642 (x : ℝ) (h₁ : (509/128:ℝ) ≤ x) (h₂ : x ≤ (1023/256:ℝ)) : (39629583/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/10000000000:ℝ) ≤ Real.pi * ((4:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((4:ℝ) - x) ≤ (736310779/10000000000:ℝ) := by nlinarith
  have hc1 : (997290454411/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (997290454411/1000000000000:ℝ) ≤ taylorCos (736310779/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((4:ℝ) - x)) ≤ (999924704101/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/10000000000:ℝ) + taylorErr ≤ (999924704101/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (613576801/50000000000:ℝ) ≤ Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (613576801/50000000000:ℝ) ≤ taylorSin (122718463/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((4:ℝ) - x)) ≤ (73564565943/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (736310779/10000000000:ℝ) + taylorErr ≤ (73564565943/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hcxl : (997290454411/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999924704101/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-73564565943/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-613576801/50000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (624636976827/50000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12554098768057/1000000000000:ℝ) := by nlinarith
  have hp1 : (20675466210773/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (20777015930591/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-61138086341/40000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-50743945667/200000000000:ℝ) := by nlinarith
  have hN : (625505091373/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (314210791756261/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (625505091373/500000000000:ℝ) (314210791756261/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (39629583/2500000000000:ℝ) ≤ ((625505091373/500000000000:ℝ)/(314210791756261/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_643 (x : ℝ) (h₁ : (509/128:ℝ) ≤ x) (h₂ : x ≤ (4:ℝ)) : (20069123/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * ((4:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((4:ℝ) - x) ≤ (736310779/10000000000:ℝ) := by nlinarith
  have hc1 : (997290454411/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (997290454411/1000000000000:ℝ) ≤ taylorCos (736310779/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((4:ℝ) - x)) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((4:ℝ) - x)) ≤ (73564565943/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (736310779/10000000000:ℝ) + taylorErr ≤ (73564565943/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hcxl : (997290454411/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (500000001131/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-73564565943/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1131/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (624636976827/50000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (314159265359/25000000000:ℝ) := by nlinarith
  have hp1 : (20675466210773/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10398662909543/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1529946246657/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (11761/250000000000:ℝ) := by nlinarith
  have hN : (997290407367/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (157413670417451/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (997290407367/1000000000000:ℝ) (157413670417451/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (20069123/2000000000000:ℝ) ≤ ((997290407367/1000000000000:ℝ)/(157413670417451/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_644 (x : ℝ) (h₁ : (1019/256:ℝ) ≤ x) (h₂ : x ≤ (4:ℝ)) : (100512239/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * ((4:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((4:ℝ) - x) ≤ (153398079/2500000000:ℝ) := by nlinarith
  have hc1 : (998118110633/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (998118110633/1000000000000:ℝ) ≤ taylorCos (153398079/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((4:ℝ) - x)) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((4:ℝ) - x)) ≤ (61320738649/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (153398079/2500000000:ℝ) + taylorErr ≤ (61320738649/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hcxl : (998118110633/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (500000001131/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-61320738649/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1131/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12505011382843/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (314159265359/25000000000:ℝ) := by nlinarith
  have hp1 : (5173944024749/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10398662909543/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1275307381151/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (11761/250000000000:ℝ) := by nlinarith
  have hN : (998118063589/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (157413670417451/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (998118063589/1000000000000:ℝ) (157413670417451/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (100512239/10000000000000:ℝ) ≤ ((998118063589/1000000000000:ℝ)/(157413670417451/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_645 (x : ℝ) (h₁ : (4077/1024:ℝ) ≤ x) (h₂ : x ≤ (1023/256:ℝ)) : (2482089/156250000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/10000000000:ℝ) ≤ Real.pi * ((4:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((4:ℝ) - x) ≤ (5829127/100000000:ℝ) := by nlinarith
  have hc1 : (249575385667/250000000000:ℝ) ≤ Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (249575385667/250000000000:ℝ) ≤ taylorCos (5829127/100000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((4:ℝ) - x)) ≤ (999924704101/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/10000000000:ℝ) + taylorErr ≤ (999924704101/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (613576801/50000000000:ℝ) ≤ Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (613576801/50000000000:ℝ) ≤ taylorSin (122718463/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((4:ℝ) - x)) ≤ (58258266823/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (5829127/100000000:ℝ) + taylorErr ≤ (58258266823/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hcxl : (249575385667/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999924704101/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-58258266823/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-613576801/50000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12508079344419/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12554098768057/1000000000000:ℝ) := by nlinarith
  have hp1 : (5175213392763/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (20777015930591/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1210432937871/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-254031270241/1000000000000:ℝ) := by nlinarith
  have hN : (1252332812909/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (314210791756261/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1252332812909/1000000000000:ℝ) (314210791756261/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2482089/156250000000:ℝ) ≤ ((1252332812909/1000000000000:ℝ)/(314210791756261/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_646 (x : ℝ) (h₁ : (4077/1024:ℝ) ≤ x) (h₂ : x ≤ (16379/4096:ℝ)) : (23464061/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (38349519/10000000000:ℝ) ≤ Real.pi * ((4:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((4:ℝ) - x) ≤ (5829127/100000000:ℝ) := by nlinarith
  have hc1 : (249575385667/250000000000:ℝ) ≤ Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (249575385667/250000000000:ℝ) ≤ taylorCos (5829127/100000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((4:ℝ) - x)) ≤ (999992648843/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (38349519/10000000000:ℝ) + taylorErr ≤ (999992648843/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (1917470119/500000000000:ℝ) ≤ Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (1917470119/500000000000:ℝ) ≤ taylorSin (38349519/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((4:ℝ) - x)) ≤ (58258266823/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (5829127/100000000:ℝ) + taylorErr ≤ (58258266823/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hcxl : (249575385667/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999992648843/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-58258266823/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-1917470119/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12508079344419/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1256253566239/100000000000:ℝ) := by nlinarith
  have hp1 : (5175213392763/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (20790978978931/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-605623200433/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-124041463/1562500000:ℝ) := by nlinarith
  have hN : (269422019747/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (157317302268821/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (269422019747/250000000000:ℝ) (157317302268821/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (23464061/2000000000000:ℝ) ≤ ((269422019747/250000000000:ℝ)/(157317302268821/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_647 (x : ℝ) (h₁ : (16317/4096:ℝ) ≤ x) (h₂ : x ≤ (4:ℝ)) : (50312709/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * ((4:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((4:ℝ) - x) ≤ (128470891/2500000000:ℝ) := by nlinarith
  have hc1 : (998679906693/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (998679906693/1000000000000:ℝ) ≤ taylorCos (128470891/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((4:ℝ) - x)) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((4:ℝ) - x)) ≤ (10273148847/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (128470891/2500000000:ℝ) + taylorErr ≤ (10273148847/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hcxl : (998679906693/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (500000001131/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-10273148847/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1131/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (2502996451593/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (314159265359/25000000000:ℝ) := by nlinarith
  have hp1 : (10356138941589/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10398662909543/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-267067529699/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (11761/250000000000:ℝ) := by nlinarith
  have hN : (998679859649/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (157413670417451/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (998679859649/1000000000000:ℝ) (157413670417451/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (50312709/5000000000000:ℝ) ≤ ((998679859649/1000000000000:ℝ)/(157413670417451/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_648 (x : ℝ) (h₁ : (8163/2048:ℝ) ≤ x) (h₂ : x ≤ (4:ℝ)) : (50346043/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * ((4:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((4:ℝ) - x) ≤ (444854429/10000000000:ℝ) := by nlinarith
  have hc1 : (99901068359/100000000000:ℝ) ≤ Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (99901068359/100000000000:ℝ) ≤ taylorCos (444854429/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((4:ℝ) - x)) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((4:ℝ) - x)) ≤ (5558846771/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (444854429/10000000000:ℝ) + taylorErr ≤ (5558846771/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hcxl : (99901068359/100000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (500000001131/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-5558846771/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1131/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1252188517151/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (314159265359/25000000000:ℝ) := by nlinarith
  have hp1 : (10361851097651/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10398662909543/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-924873179799/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (11761/250000000000:ℝ) := by nlinarith
  have hN : (499505318273/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (157413670417451/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (499505318273/500000000000:ℝ) (157413670417451/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (50346043/5000000000000:ℝ) ≤ ((499505318273/500000000000:ℝ)/(157413670417451/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_649 (x : ℝ) (h₁ : (2041/512:ℝ) ≤ x) (h₂ : x ≤ (1023/256:ℝ)) : (39782441/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/10000000000:ℝ) ≤ Real.pi * ((4:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((4:ℝ) - x) ≤ (429514621/10000000000:ℝ) := by nlinarith
  have hc1 : (999077725489/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (999077725489/1000000000000:ℝ) ≤ taylorCos (429514621/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((4:ℝ) - x)) ≤ (999924704101/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/10000000000:ℝ) + taylorErr ≤ (999924704101/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (613576801/50000000000:ℝ) ≤ Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (613576801/50000000000:ℝ) ≤ taylorSin (122718463/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((4:ℝ) - x)) ≤ (10734564809/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (429514621/10000000000:ℝ) + taylorErr ≤ (10734564809/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hcxl : (999077725489/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999924704101/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-10734564809/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-613576801/50000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6261709576149/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12554098768057/1000000000000:ℝ) := by nlinarith
  have hp1 : (2072624093133/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (20777015930591/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-892128896179/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-63585703037/250000000000:ℝ) := by nlinarith
  have hN : (1253420537637/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (314210791756261/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1253420537637/1000000000000:ℝ) (314210791756261/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (39782441/2500000000000:ℝ) ≤ ((1253420537637/1000000000000:ℝ)/(314210791756261/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_650 (x : ℝ) (h₁ : (2041/512:ℝ) ≤ x) (h₂ : x ≤ (4:ℝ)) : (100705601/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * ((4:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((4:ℝ) - x) ≤ (429514621/10000000000:ℝ) := by nlinarith
  have hc1 : (999077725489/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (999077725489/1000000000000:ℝ) ≤ taylorCos (429514621/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((4:ℝ) - x)) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((4:ℝ) - x)) ≤ (10734564809/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (429514621/10000000000:ℝ) + taylorErr ≤ (10734564809/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hcxl : (999077725489/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (500000001131/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-10734564809/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1131/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6261709576149/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (314159265359/25000000000:ℝ) := by nlinarith
  have hp1 : (2072624093133/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10398662909543/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-223250241859/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (11761/250000000000:ℝ) := by nlinarith
  have hN : (199815535689/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (157413670417451/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (199815535689/200000000000:ℝ) (157413670417451/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (100705601/10000000000000:ℝ) ≤ ((199815535689/200000000000:ℝ)/(157413670417451/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_651 (x : ℝ) (h₁ : (8165/2048:ℝ) ≤ x) (h₂ : x ≤ (4:ℝ)) : (100718643/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * ((4:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((4:ℝ) - x) ≤ (414174813/10000000000:ℝ) := by nlinarith
  have hc1 : (499571208231/500000000000:ℝ) ≤ Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (499571208231/500000000000:ℝ) ≤ taylorCos (414174813/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((4:ℝ) - x)) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((4:ℝ) - x)) ≤ (20702821633/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (414174813/10000000000:ℝ) + taylorErr ≤ (20702821633/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hcxl : (499571208231/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (500000001131/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-20702821633/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1131/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6262476566543/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (314159265359/25000000000:ℝ) := by nlinarith
  have hp1 : (10364389833679/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10398662909543/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-107640831719/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (11761/250000000000:ℝ) := by nlinarith
  have hN : (499571184709/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (157413670417451/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (499571184709/500000000000:ℝ) (157413670417451/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (100718643/10000000000000:ℝ) ≤ ((499571184709/500000000000:ℝ)/(157413670417451/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_652 (x : ℝ) (h₁ : (16339/4096:ℝ) ≤ x) (h₂ : x ≤ (4:ℝ)) : (4030859/400000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * ((4:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((4:ℝ) - x) ≤ (172572839/5000000000:ℝ) := by nlinarith
  have hc1 : (999404429169/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (999404429169/1000000000000:ℝ) ≤ taylorCos (172572839/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((4:ℝ) - x)) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((4:ℝ) - x)) ≤ (34507717859/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (172572839/5000000000:ℝ) + taylorErr ≤ (34507717859/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hcxl : (999404429169/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (500000001131/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-34507717859/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1131/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12531856046631/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (314159265359/25000000000:ℝ) := by nlinarith
  have hp1 : (20740203979483/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10398662909543/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-717668251587/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (11761/250000000000:ℝ) := by nlinarith
  have hN : (7995235057/8000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (157413670417451/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (7995235057/8000000000:ℝ) (157413670417451/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (4030859/400000000000:ℝ) ≤ ((7995235057/8000000000:ℝ)/(157413670417451/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_653 (x : ℝ) (h₁ : (4087/1024:ℝ) ≤ x) (h₂ : x ≤ (4:ℝ)) : (50407357/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * ((4:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((4:ℝ) - x) ≤ (138058271/5000000000:ℝ) := by nlinarith
  have hc1 : (999618820233/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (999618820233/1000000000000:ℝ) ≤ taylorCos (138058271/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((4:ℝ) - x)) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((4:ℝ) - x)) ≤ (27608148059/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (138058271/5000000000:ℝ) + taylorErr ≤ (27608148059/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hcxl : (999618820233/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (500000001131/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-27608148059/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1131/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12538758960177/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (314159265359/25000000000:ℝ) := by nlinarith
  have hp1 : (20751628291609/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10398662909543/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-114835130089/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (11761/250000000000:ℝ) := by nlinarith
  have hN : (999618773189/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (157413670417451/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (999618773189/1000000000000:ℝ) (157413670417451/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (50407357/5000000000000:ℝ) ≤ ((999618773189/1000000000000:ℝ)/(157413670417451/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_654 (x : ℝ) (h₁ : (16357/4096:ℝ) ≤ x) (h₂ : x ≤ (4:ℝ)) : (100848353/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * ((4:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((4:ℝ) - x) ≤ (207087407/10000000000:ℝ) := by nlinarith
  have hc1 : (99978557943/100000000000:ℝ) ≤ Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (99978557943/100000000000:ℝ) ≤ taylorCos (207087407/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((4:ℝ) - x)) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((4:ℝ) - x)) ≤ (2070726283/100000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (207087407/10000000000:ℝ) + taylorErr ≤ (2070726283/100000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hcxl : (99978557943/100000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (500000001131/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-2070726283/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1131/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6272830936861/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (314159265359/25000000000:ℝ) := by nlinarith
  have hp1 : (20763052603733/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10398662909543/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-430655691897/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (11761/250000000000:ℝ) := by nlinarith
  have hN : (499892766193/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (157413670417451/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (499892766193/500000000000:ℝ) (157413670417451/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (100848353/10000000000000:ℝ) ≤ ((499892766193/500000000000:ℝ)/(157413670417451/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_655 (x : ℝ) (h₁ : (16359/4096:ℝ) ≤ x) (h₂ : x ≤ (4:ℝ)) : (25213631/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * ((4:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((4:ℝ) - x) ≤ (191747599/10000000000:ℝ) := by nlinarith
  have hc1 : (499908083831/500000000000:ℝ) ≤ Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (499908083831/500000000000:ℝ) ≤ taylorCos (191747599/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((4:ℝ) - x)) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((4:ℝ) - x)) ≤ (9586793591/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (191747599/10000000000:ℝ) + taylorErr ≤ (9586793591/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hcxl : (499908083831/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (500000001131/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-9586793591/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1131/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1254719585451/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (314159265359/25000000000:ℝ) := by nlinarith
  have hp1 : (10382795669881/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10398662909543/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-79751867949/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (11761/250000000000:ℝ) := by nlinarith
  have hN : (499908060309/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (157413670417451/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (499908060309/500000000000:ℝ) (157413670417451/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (25213631/2500000000000:ℝ) ≤ ((499908060309/500000000000:ℝ)/(157413670417451/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_656 (x : ℝ) (h₁ : (1023/256:ℝ) ≤ x) (h₂ : x ≤ (4:ℝ)) : (100876421/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * ((4:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((4:ℝ) - x) ≤ (479369/39062500:ℝ) := by nlinarith
  have hc1 : (124990587447/125000000000:ℝ) ≤ Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (124990587447/125000000000:ℝ) ≤ taylorCos (479369/39062500:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((4:ℝ) - x)) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((4:ℝ) - x)) ≤ (2454308129/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (479369/39062500:ℝ) + taylorErr ≤ (2454308129/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hcxl : (124990587447/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (500000001131/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-2454308129/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1131/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1569262346007/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (314159265359/25000000000:ℝ) := by nlinarith
  have hp1 : (1298563478243/62500000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10398662909543/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-255215229097/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (11761/250000000000:ℝ) := by nlinarith
  have hN : (249981163133/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (157413670417451/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (249981163133/250000000000:ℝ) (157413670417451/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (100876421/10000000000000:ℝ) ≤ ((249981163133/250000000000:ℝ)/(157413670417451/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_657 (x : ℝ) (h₁ : (8185/2048:ℝ) ≤ x) (h₂ : x ≤ (4:ℝ)) : (50439991/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * ((4:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((4:ℝ) - x) ≤ (3355583/312500000:ℝ) := by nlinarith
  have hc1 : (999942347413/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (999942347413/1000000000000:ℝ) ≤ taylorCos (3355583/312500000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((4:ℝ) - x)) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((4:ℝ) - x)) ≤ (5368830757/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3355583/312500000:ℝ) + taylorErr ≤ (5368830757/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hcxl : (999942347413/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (500000001131/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-5368830757/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1131/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12555632748843/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (314159265359/25000000000:ℝ) := by nlinarith
  have hp1 : (10389777193957/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10398662909543/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-111657322521/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (11761/250000000000:ℝ) := by nlinarith
  have hN : (999942300369/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (157413670417451/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (999942300369/1000000000000:ℝ) (157413670417451/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (50439991/5000000000000:ℝ) ≤ ((999942300369/1000000000000:ℝ)/(157413670417451/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_658 (x : ℝ) (h₁ : (8189/2048:ℝ) ≤ x) (h₂ : x ≤ (4:ℝ)) : (50444739/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * ((4:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((4:ℝ) - x) ≤ (1438107/312500000:ℝ) := by nlinarith
  have hc1 : (49999470441/50000000000:ℝ) ≤ Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (49999470441/50000000000:ℝ) ≤ taylorCos (1438107/312500000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((4:ℝ) - x)) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((4:ℝ) - x)) ≤ (4601928419/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1438107/312500000:ℝ) + taylorErr ≤ (4601928419/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hcxl : (49999470441/50000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (500000001131/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-4601928419/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1131/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (2512353734399/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (314159265359/25000000000:ℝ) := by nlinarith
  have hp1 : (10394854666013/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10398662909543/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-95707804727/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (11761/250000000000:ℝ) := by nlinarith
  have hN : (62499335111/62500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (157413670417451/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (62499335111/62500000000:ℝ) (157413670417451/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (50444739/5000000000000:ℝ) ≤ ((62499335111/62500000000:ℝ)/(157413670417451/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_659 (x : ℝ) (h₁ : (16379/4096:ℝ) ≤ x) (h₂ : x ≤ (4:ℝ)) : (100890131/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * ((4:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((4:ℝ) - x) ≤ (479369/125000000:ℝ) := by nlinarith
  have hc1 : (499996322159/500000000000:ℝ) ≤ Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (499996322159/500000000000:ℝ) ≤ taylorCos (479369/125000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((4:ℝ) - x)) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((4:ℝ) - x)) ≤ (1917472431/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (479369/125000000:ℝ) + taylorErr ≤ (1917472431/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((4:ℝ) - x)) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h, cos_flip (4:ℝ) x, sin_flip (4:ℝ) x]; ring
  have hcxl : (499996322159/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (500000001131/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-1917472431/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1131/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12562535662389/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (314159265359/25000000000:ℝ) := by nlinarith
  have hp1 : (519774467501/25000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10398662909543/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-39878298897/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (11761/250000000000:ℝ) := by nlinarith
  have hN : (499996298637/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (157413670417451/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (499996298637/500000000000:ℝ) (157413670417451/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (100890131/10000000000000:ℝ) ≤ ((499996298637/500000000000:ℝ)/(157413670417451/500000000000:ℝ))^2 := by norm_num
  linarith

end Zeta23Ext.Bridge.FourPoint
