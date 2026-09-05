import FourPoint.Base

noncomputable section
open Real
namespace Zeta23Ext.Bridge.FourPoint


theorem wc_360 (x : ℝ) (h₁ : (1547/512:ℝ) ≤ x) (h₂ : x ≤ (12391/4096:ℝ)) : (29587/250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (337475773/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (395000053/5000000000:ℝ) := by nlinarith
  have hc1 : (249220279871/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (249220279871/250000000000:ℝ) ≤ taylorCos (395000053/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (997723068911/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (337475773/5000000000:ℝ) + taylorErr ≤ (997723068911/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (13488783447/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (13488783447/200000000000:ℝ) ≤ taylorSin (337475773/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (78917865301/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (395000053/5000000000:ℝ) + taylorErr ≤ (78917865301/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-997723068911/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-249220279871/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-78917865301/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-13488783447/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (2373068278859/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (4751888985673/500000000000:ℝ) := by nlinarith
  have hp1 : (15709698540307/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15728739271503/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-77579907949/62500000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1059523608139/1000000000000:ℝ) := by nlinarith
  have hN : (15450134807/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (179643591457283/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (15450134807/250000000000:ℝ) (179643591457283/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (29587/250000000000:ℝ) ≤ ((15450134807/250000000000:ℝ)/(179643591457283/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_361 (x : ℝ) (h₁ : (1547/512:ℝ) ≤ x) (h₂ : x ≤ (3099/1024:ℝ)) : (1181561/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (337475773/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (414174813/5000000000:ℝ) := by nlinarith
  have hc1 : (249142785881/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (249142785881/250000000000:ℝ) ≤ taylorCos (414174813/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (997723068911/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (337475773/5000000000:ℝ) + taylorErr ≤ (997723068911/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (13488783447/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (13488783447/200000000000:ℝ) ≤ taylorSin (337475773/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (41370133433/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (414174813/5000000000:ℝ) + taylorErr ≤ (41370133433/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-997723068911/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-249142785881/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-41370133433/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-13488783447/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (2373068278859/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2376903230829/250000000000:ℝ) := by nlinarith
  have hp1 : (15709698540307/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (7867543055829/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1301925224039/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1059523608139/1000000000000:ℝ) := by nlinarith
  have hN : (15450134807/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (179789406999211/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (15450134807/250000000000:ℝ) (179789406999211/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1181561/10000000000000:ℝ) ≤ ((15450134807/250000000000:ℝ)/(179789406999211/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_362 (x : ℝ) (h₁ : (1547/512:ℝ) ≤ x) (h₂ : x ≤ (6203/2048:ℝ)) : (235547/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (337475773/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (181009733/2000000000:ℝ) := by nlinarith
  have hc1 : (497953613577/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (497953613577/500000000000:ℝ) ≤ taylorCos (181009733/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (997723068911/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (337475773/5000000000:ℝ) + taylorErr ≤ (997723068911/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (13488783447/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (13488783447/200000000000:ℝ) ≤ taylorSin (337475773/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (18076272631/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (181009733/2000000000:ℝ) + taylorErr ≤ (18076272631/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-997723068911/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-497953613577/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-18076272631/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-13488783447/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (2373068278859/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1903056565451/200000000000:ℝ) := by nlinarith
  have hp1 : (15709698540307/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15747779791967/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1423305804263/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1059523608139/1000000000000:ℝ) := by nlinarith
  have hN : (15450134807/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (45020303641327/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (15450134807/250000000000:ℝ) (45020303641327/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (235547/2000000000000:ℝ) ≤ ((15450134807/250000000000:ℝ)/(45020303641327/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_363 (x : ℝ) (h₁ : (1547/512:ℝ) ≤ x) (h₂ : x ≤ (97/32:ℝ)) : (293481/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (337475773/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (196349541/2000000000:ℝ) := by nlinarith
  have hc1 : (995184724403/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (995184724403/1000000000000:ℝ) ≤ taylorCos (196349541/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (997723068911/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (337475773/5000000000:ℝ) + taylorErr ≤ (997723068911/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (13488783447/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (13488783447/200000000000:ℝ) ≤ taylorSin (337475773/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (98017142667/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (196349541/2000000000:ℝ) + taylorErr ≤ (98017142667/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-997723068911/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-995184724403/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-98017142667/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-13488783447/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (2373068278859/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1904590546239/200000000000:ℝ) := by nlinarith
  have hp1 : (15709698540307/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15760473472277/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-24137446513/15625000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1059523608139/1000000000000:ℝ) := by nlinarith
  have hN : (15450134807/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (180373257441149/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (15450134807/250000000000:ℝ) (180373257441149/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (293481/2500000000000:ℝ) ≤ ((15450134807/250000000000:ℝ)/(180373257441149/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_364 (x : ℝ) (h₁ : (1547/512:ℝ) ≤ x) (h₂ : x ≤ (3109/1024:ℝ)) : (1166349/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (337475773/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (141893223/1250000000:ℝ) := by nlinarith
  have hc1 : (7762219791/7812500000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (7762219791/7812500000:ℝ) ≤ taylorCos (141893223/1250000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (997723068911/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (337475773/5000000000:ℝ) + taylorErr ≤ (997723068911/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (13488783447/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (13488783447/200000000000:ℝ) ≤ taylorSin (337475773/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (14158869317/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (141893223/1250000000:ℝ) + taylorErr ≤ (14158869317/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-997723068911/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-7762219791/7812500000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-14158869317/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-13488783447/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (2373068278859/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9538292539073/1000000000000:ℝ) := by nlinarith
  have hp1 : (15709698540307/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3157172166579/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-357615904943/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1059523608139/1000000000000:ℝ) := by nlinarith
  have hN : (15450134807/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (11309878070117/62500000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (15450134807/250000000000:ℝ) (11309878070117/62500000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1166349/10000000000000:ℝ) ≤ ((15450134807/250000000000:ℝ)/(11309878070117/62500000000:ℝ))^2 := by norm_num
  linarith

theorem wc_365 (x : ℝ) (h₁ : (1547/512:ℝ) ≤ x) (h₂ : x ≤ (1557/512:ℝ)) : (231767/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (337475773/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (644271931/5000000000:ℝ) := by nlinarith
  have hc1 : (198341950281/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (198341950281/200000000000:ℝ) ≤ taylorCos (644271931/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (997723068911/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (337475773/5000000000:ℝ) + taylorErr ≤ (997723068911/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (13488783447/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (13488783447/200000000000:ℝ) ≤ taylorSin (337475773/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (128498113073/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (644271931/5000000000:ℝ) + taylorErr ≤ (128498113073/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-997723068911/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-198341950281/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-128498113073/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-13488783447/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (2373068278859/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1194204043369/125000000000:ℝ) := by nlinarith
  have hp1 : (15709698540307/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (7905624096757/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-507928889549/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1059523608139/1000000000000:ℝ) := by nlinarith
  have hN : (15450134807/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (11346486377591/62500000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (15450134807/250000000000:ℝ) (11346486377591/62500000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (231767/2000000000000:ℝ) ≤ ((15450134807/250000000000:ℝ)/(11346486377591/62500000000:ℝ))^2 := by norm_num
  linarith

theorem wc_366 (x : ℝ) (h₁ : (1547/512:ℝ) ≤ x) (h₂ : x ≤ (781/256:ℝ)) : (285997/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (337475773/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (79767001/500000000:ℝ) := by nlinarith
  have hc1 : (493650707943/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (493650707943/500000000000:ℝ) ≤ taylorCos (79767001/500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (997723068911/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (337475773/5000000000:ℝ) + taylorErr ≤ (997723068911/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (13488783447/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (13488783447/200000000000:ℝ) ≤ taylorSin (337475773/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (31771629131/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (79767001/500000000:ℝ) + taylorErr ≤ (31771629131/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-997723068911/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-493650707943/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-31771629131/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-13488783447/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (2373068278859/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (958431196271/100000000000:ℝ) := by nlinarith
  have hp1 : (15709698540307/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (247844108043/15625000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-100792461863/40000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1059523608139/1000000000000:ℝ) := by nlinarith
  have hN : (15450134807/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (182718071597093/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (15450134807/250000000000:ℝ) (182718071597093/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (285997/2500000000000:ℝ) ≤ ((15450134807/250000000000:ℝ)/(182718071597093/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_367 (x : ℝ) (h₁ : (24757/8192:ℝ) ≤ x) (h₂ : x ≤ (49529/16384:ℝ)) : (2641873/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (347063153/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (722888447/10000000000:ℝ) := by nlinarith
  have hc1 : (997388296827/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (997388296827/1000000000000:ℝ) ≤ taylorCos (722888447/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (498795956361/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (347063153/5000000000:ℝ) + taylorErr ≤ (498795956361/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (69356902111/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (69356902111/1000000000000:ℝ) ≤ taylorSin (347063153/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (72225903717/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (722888447/10000000000:ℝ) + taylorErr ≤ (72225903717/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-498795956361/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-997388296827/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-72225903717/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-69356902111/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9494190591421/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9497066805399/1000000000000:ℝ) := by nlinarith
  have hp1 : (7856435980171/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (982352018827/62500000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-8868907791/7812500000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-272449030609/250000000000:ℝ) := by nlinarith
  have hN : (46102104857/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (22423569476553/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (46102104857/500000000000:ℝ) (22423569476553/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2641873/10000000000000:ℝ) ≤ ((46102104857/500000000000:ℝ)/(22423569476553/125000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_368 (x : ℝ) (h₁ : (24757/8192:ℝ) ≤ x) (h₂ : x ≤ (24767/8192:ℝ)) : (2640801/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (347063153/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (732475827/10000000000:ℝ) := by nlinarith
  have hc1 : (249329648183/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (249329648183/250000000000:ℝ) ≤ taylorCos (732475827/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (498795956361/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (347063153/5000000000:ℝ) + taylorErr ≤ (498795956361/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (69356902111/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (69356902111/1000000000000:ℝ) ≤ taylorSin (347063153/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (1829552611/25000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (732475827/10000000000:ℝ) + taylorErr ≤ (1829552611/25000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-498795956361/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-249329648183/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-1829552611/25000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-69356902111/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9494190591421/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9498025543391/1000000000000:ℝ) := by nlinarith
  have hp1 : (7856435980171/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1571921901127/100000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-575182763699/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-272449030609/250000000000:ℝ) := by nlinarith
  have hN : (46102104857/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (22428122305727/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (46102104857/500000000000:ℝ) (22428122305727/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2640801/10000000000000:ℝ) ≤ ((46102104857/500000000000:ℝ)/(22428122305727/125000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_369 (x : ℝ) (h₁ : (24757/8192:ℝ) ≤ x) (h₂ : x ≤ (6193/2048:ℝ)) : (2638657/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (347063153/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (751650587/10000000000:ℝ) := by nlinarith
  have hc1 : (498588217233/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (498588217233/500000000000:ℝ) ≤ taylorCos (751650587/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (498795956361/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (347063153/5000000000:ℝ) + taylorErr ≤ (498795956361/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (69356902111/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (69356902111/1000000000000:ℝ) ≤ taylorSin (347063153/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (75094303203/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (751650587/10000000000:ℝ) + taylorErr ≤ (75094303203/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-498795956361/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-498588217233/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-75094303203/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-69356902111/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9494190591421/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (593746438711/62500000000:ℝ) := by nlinarith
  have hp1 : (7856435980171/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15722392431347/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1180662104317/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-272449030609/250000000000:ℝ) := by nlinarith
  have hN : (46102104857/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (89748917371391/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (46102104857/500000000000:ℝ) (89748917371391/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2638657/10000000000000:ℝ) ≤ ((46102104857/500000000000:ℝ)/(89748917371391/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_370 (x : ℝ) (h₁ : (49519/16384:ℝ) ≤ x) (h₂ : x ≤ (24767/8192:ℝ)) : (716733/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (351856843/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (732475827/10000000000:ℝ) := by nlinarith
  have hc1 : (249329648183/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (249329648183/250000000000:ℝ) ≤ taylorCos (732475827/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (19950499183/20000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (351856843/5000000000:ℝ) + taylorErr ≤ (19950499183/20000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (35156649681/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (35156649681/500000000000:ℝ) ≤ taylorSin (351856843/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (1829552611/25000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (732475827/10000000000:ℝ) + taylorErr ≤ (1829552611/25000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-19950499183/20000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-249329648183/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-1829552611/25000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-35156649681/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9495149329413/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9498025543391/1000000000000:ℝ) := by nlinarith
  have hp1 : (15714458670359/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1571921901127/100000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-575182763699/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-86323081/78125000:ℝ) := by nlinarith
  have hN : (2148209553/20000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (22428122305727/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2148209553/20000000000:ℝ) (22428122305727/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (716733/2000000000000:ℝ) ≤ ((2148209553/20000000000:ℝ)/(22428122305727/125000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_371 (x : ℝ) (h₁ : (12381/4096:ℝ) ≤ x) (h₂ : x ≤ (49539/16384:ℝ)) : (4668509/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (356650533/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (742063207/10000000000:ℝ) := by nlinarith
  have hc1 : (997247971923/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (997247971923/1000000000000:ℝ) ≤ taylorCos (742063207/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (39898283547/40000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (356650533/5000000000:ℝ) + taylorErr ≤ (39898283547/40000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (71269631983/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (71269631983/1000000000000:ℝ) ≤ taylorSin (356650533/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (14827647579/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (742063207/10000000000:ℝ) + taylorErr ≤ (14827647579/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-39898283547/40000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-997247971923/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-14827647579/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-71269631983/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (4748054033703/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1187373035173/125000000000:ℝ) := by nlinarith
  have hp1 : (7858022690189/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15720805721309/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-291378208617/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1120076770487/1000000000000:ℝ) := by nlinarith
  have hN : (30654920453/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (179461404755961/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (30654920453/250000000000:ℝ) (179461404755961/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (4668509/10000000000000:ℝ) ≤ ((30654920453/250000000000:ℝ)/(179461404755961/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_372 (x : ℝ) (h₁ : (12381/4096:ℝ) ≤ x) (h₂ : x ≤ (6193/2048:ℝ)) : (2333307/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (356650533/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (751650587/10000000000:ℝ) := by nlinarith
  have hc1 : (498588217233/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (498588217233/500000000000:ℝ) ≤ taylorCos (751650587/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (39898283547/40000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (356650533/5000000000:ℝ) + taylorErr ≤ (39898283547/40000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (71269631983/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (71269631983/1000000000000:ℝ) ≤ taylorSin (356650533/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (75094303203/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (751650587/10000000000:ℝ) + taylorErr ≤ (75094303203/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-39898283547/40000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-498588217233/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-75094303203/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-71269631983/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (4748054033703/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (593746438711/62500000000:ℝ) := by nlinarith
  have hp1 : (7858022690189/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15722392431347/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1180662104317/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1120076770487/1000000000000:ℝ) := by nlinarith
  have hN : (30654920453/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (89748917371391/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (30654920453/250000000000:ℝ) (89748917371391/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2333307/5000000000000:ℝ) ≤ ((30654920453/250000000000:ℝ)/(89748917371391/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_373 (x : ℝ) (h₁ : (12381/4096:ℝ) ≤ x) (h₂ : x ≤ (24777/8192:ℝ)) : (4662827/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (356650533/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (385412673/5000000000:ℝ) := by nlinarith
  have hc1 : (249257652469/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (249257652469/250000000000:ℝ) ≤ taylorCos (385412673/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (39898283547/40000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (356650533/5000000000:ℝ) + taylorErr ≤ (39898283547/40000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (71269631983/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (71269631983/1000000000000:ℝ) ≤ taylorSin (356650533/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (77006225767/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (385412673/5000000000:ℝ) + taylorErr ≤ (77006225767/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-39898283547/40000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-249257652469/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-77006225767/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-71269631983/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (4748054033703/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9501860495361/1000000000000:ℝ) := by nlinarith
  have hp1 : (7858022690189/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (629022634057/40000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1210966474269/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1120076770487/1000000000000:ℝ) := by nlinarith
  have hN : (30654920453/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (44892676436651/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (30654920453/250000000000:ℝ) (44892676436651/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (4662827/10000000000000:ℝ) ≤ ((30654920453/250000000000:ℝ)/(44892676436651/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_374 (x : ℝ) (h₁ : (12381/4096:ℝ) ≤ x) (h₂ : x ≤ (12391/4096:ℝ)) : (931809/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (356650533/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (395000053/5000000000:ℝ) := by nlinarith
  have hc1 : (249220279871/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (249220279871/250000000000:ℝ) ≤ taylorCos (395000053/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (39898283547/40000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (356650533/5000000000:ℝ) + taylorErr ≤ (39898283547/40000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (71269631983/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (71269631983/1000000000000:ℝ) ≤ taylorSin (356650533/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (78917865301/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (395000053/5000000000:ℝ) + taylorErr ≤ (78917865301/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-39898283547/40000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-249220279871/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-78917865301/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-71269631983/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (4748054033703/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (4751888985673/500000000000:ℝ) := by nlinarith
  have hp1 : (7858022690189/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15728739271503/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-77579907949/62500000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1120076770487/1000000000000:ℝ) := by nlinarith
  have hN : (30654920453/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (179643591457283/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (30654920453/250000000000:ℝ) (179643591457283/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (931809/2000000000000:ℝ) ≤ ((30654920453/250000000000:ℝ)/(179643591457283/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_375 (x : ℝ) (h₁ : (12381/4096:ℝ) ≤ x) (h₂ : x ≤ (3099/1024:ℝ)) : (465149/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (356650533/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (414174813/5000000000:ℝ) := by nlinarith
  have hc1 : (249142785881/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (249142785881/250000000000:ℝ) ≤ taylorCos (414174813/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (39898283547/40000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (356650533/5000000000:ℝ) + taylorErr ≤ (39898283547/40000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (71269631983/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (71269631983/1000000000000:ℝ) ≤ taylorSin (356650533/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (41370133433/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (414174813/5000000000:ℝ) + taylorErr ≤ (41370133433/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-39898283547/40000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-249142785881/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-41370133433/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-71269631983/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (4748054033703/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2376903230829/250000000000:ℝ) := by nlinarith
  have hp1 : (7858022690189/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (7867543055829/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1301925224039/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1120076770487/1000000000000:ℝ) := by nlinarith
  have hN : (30654920453/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (179789406999211/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (30654920453/250000000000:ℝ) (179789406999211/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (465149/1000000000000:ℝ) ≤ ((30654920453/250000000000:ℝ)/(179789406999211/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_376 (x : ℝ) (h₁ : (49529/16384:ℝ) ≤ x) (h₂ : x ≤ (6193/2048:ℝ)) : (737039/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (361444223/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (751650587/10000000000:ℝ) := by nlinarith
  have hc1 : (498588217233/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (498588217233/500000000000:ℝ) ≤ taylorCos (751650587/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (498694150679/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (361444223/5000000000:ℝ) + taylorErr ≤ (498694150679/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (72225899093/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (72225899093/1000000000000:ℝ) ≤ taylorSin (361444223/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (75094303203/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (751650587/10000000000:ℝ) + taylorErr ≤ (75094303203/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-498694150679/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-498588217233/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-75094303203/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-72225899093/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (4748533402699/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (593746438711/62500000000:ℝ) := by nlinarith
  have hp1 : (7858816045197/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15722392431347/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1180662104317/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1135220109341/1000000000000:ℝ) := by nlinarith
  have hN : (137831807983/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (89748917371391/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (137831807983/1000000000000:ℝ) (89748917371391/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (737039/1250000000000:ℝ) ≤ ((137831807983/1000000000000:ℝ)/(89748917371391/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_377 (x : ℝ) (h₁ : (24767/8192:ℝ) ≤ x) (h₂ : x ≤ (6193/2048:ℝ)) : (7269931/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (366237913/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (751650587/10000000000:ℝ) := by nlinarith
  have hc1 : (498588217233/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (498588217233/500000000000:ℝ) ≤ taylorCos (751650587/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (997318597263/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (366237913/5000000000:ℝ) + taylorErr ≤ (997318597263/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (9147762477/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (9147762477/125000000000:ℝ) ≤ taylorSin (366237913/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (75094303203/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (751650587/10000000000:ℝ) + taylorErr ≤ (75094303203/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-997318597263/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-498588217233/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-75094303203/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-9147762477/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (949802554339/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (593746438711/62500000000:ℝ) := by nlinarith
  have hp1 : (15719218800411/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15722392431347/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1180662104317/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1150365439281/1000000000000:ℝ) := by nlinarith
  have hN : (76523421009/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (89748917371391/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (76523421009/500000000000:ℝ) (89748917371391/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (7269931/10000000000000:ℝ) ≤ ((76523421009/500000000000:ℝ)/(89748917371391/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_378 (x : ℝ) (h₁ : (24767/8192:ℝ) ≤ x) (h₂ : x ≤ (49549/16384:ℝ)) : (7266981/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (366237913/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (380618983/5000000000:ℝ) := by nlinarith
  have hc1 : (997103980433/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (997103980433/1000000000000:ℝ) ≤ taylorCos (380618983/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (997318597263/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (366237913/5000000000:ℝ) + taylorErr ≤ (997318597263/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (9147762477/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (9147762477/125000000000:ℝ) ≤ taylorSin (366237913/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (76050299387/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (380618983/5000000000:ℝ) + taylorErr ≤ (76050299387/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-997318597263/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-997103980433/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-76050299387/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-9147762477/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (949802554339/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9500901757369/1000000000000:ℝ) := by nlinarith
  have hp1 : (15719218800411/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15723979141387/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-597906660629/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1150365439281/1000000000000:ℝ) := by nlinarith
  have hN : (76523421009/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (35906853681271/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (76523421009/500000000000:ℝ) (35906853681271/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (7266981/10000000000000:ℝ) ≤ ((76523421009/500000000000:ℝ)/(35906853681271/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_379 (x : ℝ) (h₁ : (24767/8192:ℝ) ≤ x) (h₂ : x ≤ (24777/8192:ℝ)) : (227001/312500000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (366237913/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (385412673/5000000000:ℝ) := by nlinarith
  have hc1 : (249257652469/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (249257652469/250000000000:ℝ) ≤ taylorCos (385412673/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (997318597263/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (366237913/5000000000:ℝ) + taylorErr ≤ (997318597263/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (9147762477/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (9147762477/125000000000:ℝ) ≤ taylorSin (366237913/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (77006225767/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (385412673/5000000000:ℝ) + taylorErr ≤ (77006225767/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-997318597263/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-249257652469/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-77006225767/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-9147762477/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (949802554339/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9501860495361/1000000000000:ℝ) := by nlinarith
  have hp1 : (15719218800411/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (629022634057/40000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1210966474269/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1150365439281/1000000000000:ℝ) := by nlinarith
  have hN : (76523421009/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (44892676436651/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (76523421009/500000000000:ℝ) (44892676436651/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (227001/312500000000:ℝ) ≤ ((76523421009/500000000000:ℝ)/(44892676436651/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_380 (x : ℝ) (h₁ : (24767/8192:ℝ) ≤ x) (h₂ : x ≤ (12391/4096:ℝ)) : (7258139/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (366237913/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (395000053/5000000000:ℝ) := by nlinarith
  have hc1 : (249220279871/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (249220279871/250000000000:ℝ) ≤ taylorCos (395000053/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (997318597263/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (366237913/5000000000:ℝ) + taylorErr ≤ (997318597263/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (9147762477/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (9147762477/125000000000:ℝ) ≤ taylorSin (366237913/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (78917865301/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (395000053/5000000000:ℝ) + taylorErr ≤ (78917865301/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-997318597263/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-249220279871/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-78917865301/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-9147762477/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (949802554339/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (4751888985673/500000000000:ℝ) := by nlinarith
  have hp1 : (15719218800411/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15728739271503/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-77579907949/62500000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1150365439281/1000000000000:ℝ) := by nlinarith
  have hN : (76523421009/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (179643591457283/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (76523421009/500000000000:ℝ) (179643591457283/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (7258139/10000000000000:ℝ) ≤ ((76523421009/500000000000:ℝ)/(179643591457283/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_381 (x : ℝ) (h₁ : (49539/16384:ℝ) ≤ x) (h₂ : x ≤ (49549/16384:ℝ)) : (4391993/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (371031603/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (380618983/5000000000:ℝ) := by nlinarith
  have hc1 : (997103980433/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (997103980433/1000000000000:ℝ) ≤ taylorCos (380618983/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (199449595291/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (371031603/5000000000:ℝ) + taylorErr ≤ (199449595291/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (74138233271/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (74138233271/1000000000000:ℝ) ≤ taylorSin (371031603/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (76050299387/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (380618983/5000000000:ℝ) + taylorErr ≤ (76050299387/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-199449595291/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-997103980433/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-76050299387/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-74138233271/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9498984281383/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9500901757369/1000000000000:ℝ) := by nlinarith
  have hp1 : (15720805510429/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15723979141387/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-597906660629/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-58275637307/50000000000:ℝ) := by nlinarith
  have hN : (33652953937/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (35906853681271/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (33652953937/200000000000:ℝ) (35906853681271/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (4391993/5000000000000:ℝ) ≤ ((33652953937/200000000000:ℝ)/(35906853681271/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_382 (x : ℝ) (h₁ : (49539/16384:ℝ) ≤ x) (h₂ : x ≤ (24777/8192:ℝ)) : (4390211/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (371031603/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (385412673/5000000000:ℝ) := by nlinarith
  have hc1 : (249257652469/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (249257652469/250000000000:ℝ) ≤ taylorCos (385412673/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (199449595291/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (371031603/5000000000:ℝ) + taylorErr ≤ (199449595291/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (74138233271/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (74138233271/1000000000000:ℝ) ≤ taylorSin (371031603/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (77006225767/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (385412673/5000000000:ℝ) + taylorErr ≤ (77006225767/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-199449595291/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-249257652469/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-77006225767/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-74138233271/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9498984281383/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9501860495361/1000000000000:ℝ) := by nlinarith
  have hp1 : (15720805510429/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (629022634057/40000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1210966474269/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-58275637307/50000000000:ℝ) := by nlinarith
  have hN : (33652953937/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (44892676436651/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (33652953937/200000000000:ℝ) (44892676436651/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (4390211/5000000000000:ℝ) ≤ ((33652953937/200000000000:ℝ)/(44892676436651/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_383 (x : ℝ) (h₁ : (6193/2048:ℝ) ≤ x) (h₂ : x ≤ (24777/8192:ℝ)) : (5220389/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (375825293/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (385412673/5000000000:ℝ) := by nlinarith
  have hc1 : (249257652469/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (249257652469/250000000000:ℝ) ≤ taylorCos (385412673/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (498588219499/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (375825293/5000000000:ℝ) + taylorErr ≤ (498588219499/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (75094298579/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (75094298579/1000000000000:ℝ) ≤ taylorSin (375825293/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (77006225767/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (385412673/5000000000:ℝ) + taylorErr ≤ (77006225767/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-498588219499/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-249257652469/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-77006225767/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-75094298579/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15199908831/1600000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9501860495361/1000000000000:ℝ) := by nlinarith
  have hp1 : (7861196110223/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (629022634057/40000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1210966474269/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-590331007889/500000000000:ℝ) := by nlinarith
  have hN : (9174278839/50000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (44892676436651/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (9174278839/50000000000:ℝ) (44892676436651/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (5220389/5000000000000:ℝ) ≤ ((9174278839/50000000000:ℝ)/(44892676436651/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_384 (x : ℝ) (h₁ : (6193/2048:ℝ) ≤ x) (h₂ : x ≤ (49559/16384:ℝ)) : (5218271/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (375825293/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (390206363/5000000000:ℝ) := by nlinarith
  have hc1 : (996956322871/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (996956322871/1000000000000:ℝ) ≤ taylorCos (390206363/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (498588219499/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (375825293/5000000000:ℝ) + taylorErr ≤ (498588219499/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (75094298579/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (75094298579/1000000000000:ℝ) ≤ taylorSin (375825293/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (19490520341/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (390206363/5000000000:ℝ) + taylorErr ≤ (19490520341/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-498588219499/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-996956322871/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-19490520341/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-75094298579/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15199908831/1600000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (4751409616677/500000000000:ℝ) := by nlinarith
  have hp1 : (7861196110223/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3145430512293/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1226121547621/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-590331007889/500000000000:ℝ) := by nlinarith
  have hN : (9174278839/50000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (89803573381803/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (9174278839/50000000000:ℝ) (89803573381803/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (5218271/5000000000000:ℝ) ≤ ((9174278839/50000000000:ℝ)/(89803573381803/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_385 (x : ℝ) (h₁ : (6193/2048:ℝ) ≤ x) (h₂ : x ≤ (12391/4096:ℝ)) : (2608077/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (375825293/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (395000053/5000000000:ℝ) := by nlinarith
  have hc1 : (249220279871/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (249220279871/250000000000:ℝ) ≤ taylorCos (395000053/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (498588219499/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (375825293/5000000000:ℝ) + taylorErr ≤ (498588219499/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (75094298579/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (75094298579/1000000000000:ℝ) ≤ taylorSin (375825293/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (78917865301/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (395000053/5000000000:ℝ) + taylorErr ≤ (78917865301/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-498588219499/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-249220279871/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-78917865301/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-75094298579/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15199908831/1600000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (4751888985673/500000000000:ℝ) := by nlinarith
  have hp1 : (7861196110223/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15728739271503/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-77579907949/62500000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-590331007889/500000000000:ℝ) := by nlinarith
  have hN : (9174278839/50000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (179643591457283/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (9174278839/50000000000:ℝ) (179643591457283/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2608077/2500000000000:ℝ) ≤ ((9174278839/50000000000:ℝ)/(179643591457283/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_386 (x : ℝ) (h₁ : (6193/2048:ℝ) ≤ x) (h₂ : x ≤ (24787/8192:ℝ)) : (5211923/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (375825293/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (404587433/5000000000:ℝ) := by nlinarith
  have hc1 : (199345592769/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (199345592769/200000000000:ℝ) ≤ taylorCos (404587433/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (498588219499/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (375825293/5000000000:ℝ) + taylorErr ≤ (498588219499/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (75094298579/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (75094298579/1000000000000:ℝ) ≤ taylorSin (375825293/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (20207303669/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (404587433/5000000000:ℝ) + taylorErr ≤ (20207303669/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-498588219499/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-199345592769/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-20207303669/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-75094298579/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15199908831/1600000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9505695447331/1000000000000:ℝ) := by nlinarith
  have hp1 : (7861196110223/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (786595634579/50000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-317899537053/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-590331007889/500000000000:ℝ) := by nlinarith
  have hN : (9174278839/50000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (179716491874819/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (9174278839/50000000000:ℝ) (179716491874819/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (5211923/5000000000000:ℝ) ≤ ((9174278839/50000000000:ℝ)/(179716491874819/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_387 (x : ℝ) (h₁ : (6193/2048:ℝ) ≤ x) (h₂ : x ≤ (3099/1024:ℝ)) : (10415393/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (375825293/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (414174813/5000000000:ℝ) := by nlinarith
  have hc1 : (249142785881/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (249142785881/250000000000:ℝ) ≤ taylorCos (414174813/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (498588219499/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (375825293/5000000000:ℝ) + taylorErr ≤ (498588219499/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (75094298579/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (75094298579/1000000000000:ℝ) ≤ taylorSin (375825293/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (41370133433/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (414174813/5000000000:ℝ) + taylorErr ≤ (41370133433/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-498588219499/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-249142785881/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-41370133433/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-75094298579/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15199908831/1600000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2376903230829/250000000000:ℝ) := by nlinarith
  have hp1 : (7861196110223/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (7867543055829/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1301925224039/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-590331007889/500000000000:ℝ) := by nlinarith
  have hN : (9174278839/50000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (179789406999211/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (9174278839/50000000000:ℝ) (179789406999211/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (10415393/10000000000000:ℝ) ≤ ((9174278839/50000000000:ℝ)/(179789406999211/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_388 (x : ℝ) (h₁ : (6193/2048:ℝ) ≤ x) (h₂ : x ≤ (12401/4096:ℝ)) : (649907/625000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (375825293/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (433349573/5000000000:ℝ) := by nlinarith
  have hc1 : (996246511153/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (996246511153/1000000000000:ℝ) ≤ taylorCos (433349573/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (498588219499/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (375825293/5000000000:ℝ) + taylorErr ≤ (498588219499/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (75094298579/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (75094298579/1000000000000:ℝ) ≤ taylorSin (375825293/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (86561451583/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (433349573/5000000000:ℝ) + taylorErr ≤ (86561451583/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-498588219499/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-996246511153/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-86561451583/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-75094298579/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15199908831/1600000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1902289575057/200000000000:ℝ) := by nlinarith
  have hp1 : (7861196110223/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15741432951811/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-681300643153/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-590331007889/500000000000:ℝ) := by nlinarith
  have hN : (9174278839/50000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (11245955085533/62500000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (9174278839/50000000000:ℝ) (11245955085533/62500000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (649907/625000000000:ℝ) ≤ ((9174278839/50000000000:ℝ)/(11245955085533/62500000000:ℝ))^2 := by norm_num
  linarith

theorem wc_389 (x : ℝ) (h₁ : (6193/2048:ℝ) ≤ x) (h₂ : x ≤ (6203/2048:ℝ)) : (2076333/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (375825293/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (181009733/2000000000:ℝ) := by nlinarith
  have hc1 : (497953613577/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (497953613577/500000000000:ℝ) ≤ taylorCos (181009733/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (498588219499/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (375825293/5000000000:ℝ) + taylorErr ≤ (498588219499/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (75094298579/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (75094298579/1000000000000:ℝ) ≤ taylorSin (375825293/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (18076272631/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (181009733/2000000000:ℝ) + taylorErr ≤ (18076272631/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-498588219499/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-497953613577/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-18076272631/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-75094298579/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15199908831/1600000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1903056565451/200000000000:ℝ) := by nlinarith
  have hp1 : (7861196110223/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15747779791967/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1423305804263/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-590331007889/500000000000:ℝ) := by nlinarith
  have hN : (9174278839/50000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (45020303641327/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (9174278839/50000000000:ℝ) (45020303641327/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2076333/2000000000000:ℝ) ≤ ((9174278839/50000000000:ℝ)/(45020303641327/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_390 (x : ℝ) (h₁ : (6193/2048:ℝ) ≤ x) (h₂ : x ≤ (97/32:ℝ)) : (5174037/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (375825293/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (196349541/2000000000:ℝ) := by nlinarith
  have hc1 : (995184724403/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (995184724403/1000000000000:ℝ) ≤ taylorCos (196349541/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (498588219499/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (375825293/5000000000:ℝ) + taylorErr ≤ (498588219499/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (75094298579/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (75094298579/1000000000000:ℝ) ≤ taylorSin (375825293/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (98017142667/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (196349541/2000000000:ℝ) + taylorErr ≤ (98017142667/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-498588219499/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-995184724403/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-98017142667/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-75094298579/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15199908831/1600000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1904590546239/200000000000:ℝ) := by nlinarith
  have hp1 : (7861196110223/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15760473472277/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-24137446513/15625000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-590331007889/500000000000:ℝ) := by nlinarith
  have hN : (9174278839/50000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (180373257441149/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (9174278839/50000000000:ℝ) (180373257441149/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (5174037/5000000000000:ℝ) ≤ ((9174278839/50000000000:ℝ)/(180373257441149/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_391 (x : ℝ) (h₁ : (49549/16384:ℝ) ≤ x) (h₂ : x ≤ (49559/16384:ℝ)) : (12240211/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (152247593/2000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (390206363/5000000000:ℝ) := by nlinarith
  have hc1 : (996956322871/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (996956322871/1000000000000:ℝ) ≤ taylorCos (390206363/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (199420796993/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (152247593/2000000000:ℝ) + taylorErr ≤ (199420796993/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (76050294763/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (76050294763/1000000000000:ℝ) ≤ taylorSin (152247593/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (19490520341/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (390206363/5000000000:ℝ) + taylorErr ≤ (19490520341/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-199420796993/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-996956322871/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-19490520341/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-76050294763/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1187612719671/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (4751409616677/500000000000:ℝ) := by nlinarith
  have hp1 : (491374341577/31250000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3145430512293/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1226121547621/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-298953308127/250000000000:ℝ) := by nlinarith
  have hN : (198709247543/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (89803573381803/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (198709247543/1000000000000:ℝ) (89803573381803/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (12240211/10000000000000:ℝ) ≤ ((198709247543/1000000000000:ℝ)/(89803573381803/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_392 (x : ℝ) (h₁ : (49549/16384:ℝ) ≤ x) (h₂ : x ≤ (12391/4096:ℝ)) : (2447049/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (152247593/2000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (395000053/5000000000:ℝ) := by nlinarith
  have hc1 : (249220279871/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (249220279871/250000000000:ℝ) ≤ taylorCos (395000053/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (199420796993/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (152247593/2000000000:ℝ) + taylorErr ≤ (199420796993/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (76050294763/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (76050294763/1000000000000:ℝ) ≤ taylorSin (152247593/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (78917865301/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (395000053/5000000000:ℝ) + taylorErr ≤ (78917865301/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-199420796993/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-249220279871/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-78917865301/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-76050294763/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1187612719671/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (4751888985673/500000000000:ℝ) := by nlinarith
  have hp1 : (491374341577/31250000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15728739271503/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-77579907949/62500000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-298953308127/250000000000:ℝ) := by nlinarith
  have hN : (198709247543/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (179643591457283/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (198709247543/1000000000000:ℝ) (179643591457283/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2447049/2000000000000:ℝ) ≤ ((198709247543/1000000000000:ℝ)/(179643591457283/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_393 (x : ℝ) (h₁ : (24777/8192:ℝ) ≤ x) (h₂ : x ≤ (12391/4096:ℝ)) : (14182191/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (154165069/2000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (395000053/5000000000:ℝ) := by nlinarith
  have hc1 : (249220279871/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (249220279871/250000000000:ℝ) ≤ taylorCos (395000053/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (124628826801/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (154165069/2000000000:ℝ) + taylorErr ≤ (124628826801/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (77006221143/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (77006221143/1000000000000:ℝ) ≤ taylorSin (154165069/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (78917865301/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (395000053/5000000000:ℝ) + taylorErr ≤ (78917865301/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-124628826801/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-249220279871/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-78917865301/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-77006221143/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (463958032/48828125:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (4751888985673/500000000000:ℝ) := by nlinarith
  have hp1 : (15725565640481/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15728739271503/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-77579907949/62500000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1210966385309/1000000000000:ℝ) := by nlinarith
  have hN : (213935770901/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (179643591457283/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (213935770901/1000000000000:ℝ) (179643591457283/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (14182191/10000000000000:ℝ) ≤ ((213935770901/1000000000000:ℝ)/(179643591457283/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_394 (x : ℝ) (h₁ : (24777/8192:ℝ) ≤ x) (h₂ : x ≤ (49569/16384:ℝ)) : (7088219/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (154165069/2000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (399793743/5000000000:ℝ) := by nlinarith
  have hc1 : (199360999957/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (199360999957/200000000000:ℝ) ≤ taylorCos (399793743/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (124628826801/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (154165069/2000000000:ℝ) + taylorErr ≤ (124628826801/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (77006221143/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (77006221143/1000000000000:ℝ) ≤ taylorSin (154165069/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (79873576697/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (399793743/5000000000:ℝ) + taylorErr ≤ (79873576697/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-124628826801/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-199360999957/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-79873576697/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-77006221143/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (463958032/48828125:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (4752368354669/500000000000:ℝ) := by nlinarith
  have hp1 : (15725565640481/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15730325981541/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-314109349689/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1210966385309/1000000000000:ℝ) := by nlinarith
  have hN : (213935770901/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (7187201593107/40000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (213935770901/1000000000000:ℝ) (7187201593107/40000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (7088219/5000000000000:ℝ) ≤ ((213935770901/1000000000000:ℝ)/(7187201593107/40000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_395 (x : ℝ) (h₁ : (24777/8192:ℝ) ≤ x) (h₂ : x ≤ (24787/8192:ℝ)) : (221417/156250000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (154165069/2000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (404587433/5000000000:ℝ) := by nlinarith
  have hc1 : (199345592769/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (199345592769/200000000000:ℝ) ≤ taylorCos (404587433/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (124628826801/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (154165069/2000000000:ℝ) + taylorErr ≤ (124628826801/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (77006221143/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (77006221143/1000000000000:ℝ) ≤ taylorSin (154165069/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (20207303669/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (404587433/5000000000:ℝ) + taylorErr ≤ (20207303669/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-124628826801/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-199345592769/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-20207303669/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-77006221143/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (463958032/48828125:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9505695447331/1000000000000:ℝ) := by nlinarith
  have hp1 : (15725565640481/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (786595634579/50000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-317899537053/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1210966385309/1000000000000:ℝ) := by nlinarith
  have hN : (213935770901/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (179716491874819/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (213935770901/1000000000000:ℝ) (179716491874819/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (221417/156250000000:ℝ) ≤ ((213935770901/1000000000000:ℝ)/(179716491874819/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_396 (x : ℝ) (h₁ : (24777/8192:ℝ) ≤ x) (h₂ : x ≤ (3099/1024:ℝ)) : (3539799/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (154165069/2000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (414174813/5000000000:ℝ) := by nlinarith
  have hc1 : (249142785881/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (249142785881/250000000000:ℝ) ≤ taylorCos (414174813/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (124628826801/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (154165069/2000000000:ℝ) + taylorErr ≤ (124628826801/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (77006221143/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (77006221143/1000000000000:ℝ) ≤ taylorSin (154165069/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (41370133433/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (414174813/5000000000:ℝ) + taylorErr ≤ (41370133433/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-124628826801/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-249142785881/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-41370133433/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-77006221143/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (463958032/48828125:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2376903230829/250000000000:ℝ) := by nlinarith
  have hp1 : (15725565640481/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (7867543055829/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1301925224039/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1210966385309/1000000000000:ℝ) := by nlinarith
  have hN : (213935770901/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (179789406999211/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (213935770901/1000000000000:ℝ) (179789406999211/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (3539799/2500000000000:ℝ) ≤ ((213935770901/1000000000000:ℝ)/(179789406999211/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_397 (x : ℝ) (h₁ : (49559/16384:ℝ) ≤ x) (h₂ : x ≤ (49569/16384:ℝ)) : (16266623/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (31216509/400000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (399793743/5000000000:ℝ) := by nlinarith
  have hc1 : (199360999957/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (199360999957/200000000000:ℝ) ≤ taylorCos (399793743/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (996956327403/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (31216509/400000000:ℝ) + taylorErr ≤ (996956327403/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (3898103837/50000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (3898103837/50000000000:ℝ) ≤ taylorSin (31216509/400000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (79873576697/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (399793743/5000000000:ℝ) + taylorErr ≤ (79873576697/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-996956327403/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-199360999957/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-79873576697/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-3898103837/50000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9502819233353/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (4752368354669/500000000000:ℝ) := by nlinarith
  have hp1 : (15727152350499/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15730325981541/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-314109349689/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1226121458451/1000000000000:ℝ) := by nlinarith
  have hN : (28645641381/125000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (7187201593107/40000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (28645641381/125000000000:ℝ) (7187201593107/40000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (16266623/10000000000000:ℝ) ≤ ((28645641381/125000000000:ℝ)/(7187201593107/40000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_398 (x : ℝ) (h₁ : (49559/16384:ℝ) ≤ x) (h₂ : x ≤ (24787/8192:ℝ)) : (650401/400000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (31216509/400000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (404587433/5000000000:ℝ) := by nlinarith
  have hc1 : (199345592769/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (199345592769/200000000000:ℝ) ≤ taylorCos (404587433/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (996956327403/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (31216509/400000000:ℝ) + taylorErr ≤ (996956327403/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (3898103837/50000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (3898103837/50000000000:ℝ) ≤ taylorSin (31216509/400000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (20207303669/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (404587433/5000000000:ℝ) + taylorErr ≤ (20207303669/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-996956327403/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-199345592769/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-20207303669/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-3898103837/50000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9502819233353/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9505695447331/1000000000000:ℝ) := by nlinarith
  have hp1 : (15727152350499/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (786595634579/50000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-317899537053/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1226121458451/1000000000000:ℝ) := by nlinarith
  have hN : (28645641381/125000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (179716491874819/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (28645641381/125000000000:ℝ) (179716491874819/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (650401/400000000000:ℝ) ≤ ((28645641381/125000000000:ℝ)/(179716491874819/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_399 (x : ℝ) (h₁ : (12391/4096:ℝ) ≤ x) (h₂ : x ≤ (24787/8192:ℝ)) : (18493409/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (158000021/2000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (404587433/5000000000:ℝ) := by nlinarith
  have hc1 : (199345592769/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (199345592769/200000000000:ℝ) ≤ taylorCos (404587433/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (62305070251/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (158000021/2000000000:ℝ) + taylorErr ≤ (62305070251/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (78917860677/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (78917860677/1000000000000:ℝ) ≤ taylorSin (158000021/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (20207303669/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (404587433/5000000000:ℝ) + taylorErr ≤ (20207303669/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-62305070251/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-199345592769/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-20207303669/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-78917860677/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1900755594269/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9505695447331/1000000000000:ℝ) := by nlinarith
  have hp1 : (3932184765129/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (786595634579/50000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-317899537053/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-620639218901/500000000000:ℝ) := by nlinarith
  have hN : (122198656893/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (179716491874819/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (122198656893/500000000000:ℝ) (179716491874819/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (18493409/10000000000000:ℝ) ≤ ((122198656893/500000000000:ℝ)/(179716491874819/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_400 (x : ℝ) (h₁ : (12391/4096:ℝ) ≤ x) (h₂ : x ≤ (49579/16384:ℝ)) : (18485909/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (158000021/2000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (409381123/5000000000:ℝ) := by nlinarith
  have hc1 : (498325005867/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (498325005867/500000000000:ℝ) ≤ taylorCos (409381123/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (62305070251/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (158000021/2000000000:ℝ) + taylorErr ≤ (62305070251/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (78917860677/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (78917860677/1000000000000:ℝ) ≤ taylorSin (158000021/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (40892389179/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (409381123/5000000000:ℝ) + taylorErr ≤ (40892389179/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-62305070251/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-498325005867/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-40892389179/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-78917860677/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1900755594269/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9506654185323/1000000000000:ℝ) := by nlinarith
  have hp1 : (3932184765129/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (7866749700809/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-643380380679/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-620639218901/500000000000:ℝ) := by nlinarith
  have hN : (122198656893/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (179752947598639/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (122198656893/500000000000:ℝ) (179752947598639/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (18485909/10000000000000:ℝ) ≤ ((122198656893/500000000000:ℝ)/(179752947598639/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_401 (x : ℝ) (h₁ : (12391/4096:ℝ) ≤ x) (h₂ : x ≤ (3099/1024:ℝ)) : (4619603/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (158000021/2000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (414174813/5000000000:ℝ) := by nlinarith
  have hc1 : (249142785881/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (249142785881/250000000000:ℝ) ≤ taylorCos (414174813/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (62305070251/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (158000021/2000000000:ℝ) + taylorErr ≤ (62305070251/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (78917860677/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (78917860677/1000000000000:ℝ) ≤ taylorSin (158000021/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (41370133433/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (414174813/5000000000:ℝ) + taylorErr ≤ (41370133433/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-62305070251/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-249142785881/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-41370133433/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-78917860677/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1900755594269/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2376903230829/250000000000:ℝ) := by nlinarith
  have hp1 : (3932184765129/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (7867543055829/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1301925224039/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-620639218901/500000000000:ℝ) := by nlinarith
  have hN : (122198656893/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (179789406999211/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (122198656893/500000000000:ℝ) (179789406999211/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (4619603/2500000000000:ℝ) ≤ ((122198656893/500000000000:ℝ)/(179789406999211/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_402 (x : ℝ) (h₁ : (12391/4096:ℝ) ≤ x) (h₂ : x ≤ (24797/8192:ℝ)) : (1846343/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (158000021/2000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (423762193/5000000000:ℝ) := by nlinarith
  have hc1 : (124551332387/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (124551332387/125000000000:ℝ) ≤ taylorCos (423762193/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (62305070251/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (158000021/2000000000:ℝ) + taylorErr ≤ (62305070251/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (78917860677/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (78917860677/1000000000000:ℝ) ≤ taylorSin (158000021/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (84651014843/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (423762193/5000000000:ℝ) + taylorErr ≤ (84651014843/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-62305070251/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-124551332387/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-84651014843/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-78917860677/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1900755594269/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9509530399301/1000000000000:ℝ) := by nlinarith
  have hp1 : (3932184765129/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3147651906347/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-166532455153/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-620639218901/500000000000:ℝ) := by nlinarith
  have hN : (122198656893/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (8993116841523/50000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (122198656893/500000000000:ℝ) (8993116841523/50000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1846343/1000000000000:ℝ) ≤ ((122198656893/500000000000:ℝ)/(8993116841523/50000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_403 (x : ℝ) (h₁ : (12391/4096:ℝ) ≤ x) (h₂ : x ≤ (12401/4096:ℝ)) : (18448463/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (158000021/2000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (433349573/5000000000:ℝ) := by nlinarith
  have hc1 : (996246511153/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (996246511153/1000000000000:ℝ) ≤ taylorCos (433349573/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (62305070251/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (158000021/2000000000:ℝ) + taylorErr ≤ (62305070251/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (78917860677/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (78917860677/1000000000000:ℝ) ≤ taylorSin (158000021/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (86561451583/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (433349573/5000000000:ℝ) + taylorErr ≤ (86561451583/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-62305070251/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-996246511153/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-86561451583/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-78917860677/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1900755594269/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1902289575057/200000000000:ℝ) := by nlinarith
  have hp1 : (3932184765129/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15741432951811/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-681300643153/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-620639218901/500000000000:ℝ) := by nlinarith
  have hN : (122198656893/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (11245955085533/62500000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (122198656893/500000000000:ℝ) (11245955085533/62500000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (18448463/10000000000000:ℝ) ≤ ((122198656893/500000000000:ℝ)/(11245955085533/62500000000:ℝ))^2 := by norm_num
  linarith

theorem wc_404 (x : ℝ) (h₁ : (12391/4096:ℝ) ≤ x) (h₂ : x ≤ (6203/2048:ℝ)) : (736743/400000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (158000021/2000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (181009733/2000000000:ℝ) := by nlinarith
  have hc1 : (497953613577/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (497953613577/500000000000:ℝ) ≤ taylorCos (181009733/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (62305070251/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (158000021/2000000000:ℝ) + taylorErr ≤ (62305070251/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (78917860677/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (78917860677/1000000000000:ℝ) ≤ taylorSin (158000021/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (18076272631/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (181009733/2000000000:ℝ) + taylorErr ≤ (18076272631/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-62305070251/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-497953613577/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-18076272631/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-78917860677/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1900755594269/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1903056565451/200000000000:ℝ) := by nlinarith
  have hp1 : (3932184765129/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15747779791967/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1423305804263/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-620639218901/500000000000:ℝ) := by nlinarith
  have hN : (122198656893/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (45020303641327/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (122198656893/500000000000:ℝ) (45020303641327/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (736743/400000000000:ℝ) ≤ ((122198656893/500000000000:ℝ)/(45020303641327/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_405 (x : ℝ) (h₁ : (49569/16384:ℝ) ≤ x) (h₂ : x ≤ (49579/16384:ℝ)) : (4172491/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (159917497/2000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (409381123/5000000000:ℝ) := by nlinarith
  have hc1 : (498325005867/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (498325005867/500000000000:ℝ) ≤ taylorCos (409381123/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (498402502159/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (159917497/2000000000:ℝ) + taylorErr ≤ (498402502159/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (79873572073/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (79873572073/1000000000000:ℝ) ≤ taylorSin (159917497/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (40892389179/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (409381123/5000000000:ℝ) + taylorErr ≤ (40892389179/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-498402502159/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-498325005867/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-40892389179/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-79873572073/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9504736709337/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9506654185323/1000000000000:ℝ) := by nlinarith
  have hp1 : (15730325770533/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (7866749700809/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-643380380679/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-314109327291/250000000000:ℝ) := by nlinarith
  have hN : (129816152423/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (179752947598639/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (129816152423/500000000000:ℝ) (179752947598639/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (4172491/2000000000000:ℝ) ≤ ((129816152423/500000000000:ℝ)/(179752947598639/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_406 (x : ℝ) (h₁ : (49569/16384:ℝ) ≤ x) (h₂ : x ≤ (3099/1024:ℝ)) : (10426997/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (159917497/2000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (414174813/5000000000:ℝ) := by nlinarith
  have hc1 : (249142785881/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (249142785881/250000000000:ℝ) ≤ taylorCos (414174813/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (498402502159/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (159917497/2000000000:ℝ) + taylorErr ≤ (498402502159/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (79873572073/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (79873572073/1000000000000:ℝ) ≤ taylorSin (159917497/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (41370133433/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (414174813/5000000000:ℝ) + taylorErr ≤ (41370133433/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-498402502159/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-249142785881/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-41370133433/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-79873572073/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9504736709337/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2376903230829/250000000000:ℝ) := by nlinarith
  have hp1 : (15730325770533/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (7867543055829/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1301925224039/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-314109327291/250000000000:ℝ) := by nlinarith
  have hN : (129816152423/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (179789406999211/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (129816152423/500000000000:ℝ) (179789406999211/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (10426997/5000000000000:ℝ) ≤ ((129816152423/500000000000:ℝ)/(179789406999211/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_407 (x : ℝ) (h₁ : (24787/8192:ℝ) ≤ x) (h₂ : x ≤ (3099/1024:ℝ)) : (11686831/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (161834973/2000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (414174813/5000000000:ℝ) := by nlinarith
  have hc1 : (249142785881/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (249142785881/250000000000:ℝ) ≤ taylorCos (414174813/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (498363984189/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (161834973/2000000000:ℝ) + taylorErr ≤ (498363984189/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (20207302513/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (20207302513/250000000000:ℝ) ≤ taylorSin (161834973/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (41370133433/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (414174813/5000000000:ℝ) + taylorErr ≤ (41370133433/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-498363984189/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-249142785881/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-41370133433/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-20207302513/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (950569544733/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2376903230829/250000000000:ℝ) := by nlinarith
  have hp1 : (15731912480551/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (7867543055829/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1301925224039/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-127159805841/100000000000:ℝ) := by nlinarith
  have hN : (17179380627/62500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (179789406999211/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (17179380627/62500000000:ℝ) (179789406999211/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (11686831/5000000000000:ℝ) ≤ ((17179380627/62500000000:ℝ)/(179789406999211/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_408 (x : ℝ) (h₁ : (24787/8192:ℝ) ≤ x) (h₂ : x ≤ (49589/16384:ℝ)) : (2920523/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (161834973/2000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (418968503/5000000000:ℝ) := by nlinarith
  have hc1 : (996491359287/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (996491359287/1000000000000:ℝ) ≤ taylorCos (418968503/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (498363984189/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (161834973/2000000000:ℝ) + taylorErr ≤ (498363984189/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (20207302513/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (20207302513/250000000000:ℝ) ≤ taylorSin (161834973/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (2092391983/25000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (418968503/5000000000:ℝ) + taylorErr ≤ (2092391983/25000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-498363984189/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-996491359287/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-2092391983/25000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-20207302513/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (950569544733/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2377142915327/250000000000:ℝ) := by nlinarith
  have hp1 : (15731912480551/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (245885512839/15625000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1317091522049/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-127159805841/100000000000:ℝ) := by nlinarith
  have hN : (17179380627/62500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (8991293503823/50000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (17179380627/62500000000:ℝ) (8991293503823/50000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2920523/1250000000000:ℝ) ≤ ((17179380627/62500000000:ℝ)/(8991293503823/50000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_409 (x : ℝ) (h₁ : (24787/8192:ℝ) ≤ x) (h₂ : x ≤ (24797/8192:ℝ)) : (23354711/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (161834973/2000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (423762193/5000000000:ℝ) := by nlinarith
  have hc1 : (124551332387/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (124551332387/125000000000:ℝ) ≤ taylorCos (423762193/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (498363984189/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (161834973/2000000000:ℝ) + taylorErr ≤ (498363984189/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (20207302513/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (20207302513/250000000000:ℝ) ≤ taylorSin (161834973/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (84651014843/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (423762193/5000000000:ℝ) + taylorErr ≤ (84651014843/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-498363984189/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-124551332387/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-84651014843/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-20207302513/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (950569544733/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9509530399301/1000000000000:ℝ) := by nlinarith
  have hp1 : (15731912480551/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3147651906347/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-166532455153/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-127159805841/100000000000:ℝ) := by nlinarith
  have hN : (17179380627/62500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (8993116841523/50000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (17179380627/62500000000:ℝ) (8993116841523/50000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (23354711/10000000000000:ℝ) ≤ ((17179380627/62500000000:ℝ)/(8993116841523/50000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_410 (x : ℝ) (h₁ : (24787/8192:ℝ) ≤ x) (h₂ : x ≤ (12401/4096:ℝ)) : (23335779/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (161834973/2000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (433349573/5000000000:ℝ) := by nlinarith
  have hc1 : (996246511153/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (996246511153/1000000000000:ℝ) ≤ taylorCos (433349573/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (498363984189/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (161834973/2000000000:ℝ) + taylorErr ≤ (498363984189/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (20207302513/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (20207302513/250000000000:ℝ) ≤ taylorSin (161834973/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (86561451583/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (433349573/5000000000:ℝ) + taylorErr ≤ (86561451583/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-498363984189/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-996246511153/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-86561451583/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-20207302513/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (950569544733/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1902289575057/200000000000:ℝ) := by nlinarith
  have hp1 : (15731912480551/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15741432951811/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-681300643153/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-127159805841/100000000000:ℝ) := by nlinarith
  have hN : (17179380627/62500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (11245955085533/62500000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (17179380627/62500000000:ℝ) (11245955085533/62500000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (23335779/10000000000000:ℝ) ≤ ((17179380627/62500000000:ℝ)/(11245955085533/62500000000:ℝ))^2 := by norm_num
  linarith

theorem wc_411 (x : ℝ) (h₁ : (49579/16384:ℝ) ≤ x) (h₂ : x ≤ (49589/16384:ℝ)) : (13013467/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (163752449/2000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (418968503/5000000000:ℝ) := by nlinarith
  have hc1 : (996491359287/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (996491359287/1000000000000:ℝ) ≤ taylorCos (418968503/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (996650016267/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (163752449/2000000000:ℝ) + taylorErr ≤ (996650016267/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (40892386867/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (40892386867/500000000000:ℝ) ≤ taylorSin (163752449/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (2092391983/25000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (418968503/5000000000:ℝ) + taylorErr ≤ (2092391983/25000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-996650016267/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-996491359287/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-2092391983/25000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-40892386867/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (4753327092661/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2377142915327/250000000000:ℝ) := by nlinarith
  have hp1 : (1966687398821/125000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (245885512839/15625000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1317091522049/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-80422541959/62500000000:ℝ) := by nlinarith
  have hN : (290110655077/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (8991293503823/50000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (290110655077/1000000000000:ℝ) (8991293503823/50000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (13013467/5000000000000:ℝ) ≤ ((290110655077/1000000000000:ℝ)/(8991293503823/50000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_412 (x : ℝ) (h₁ : (49579/16384:ℝ) ≤ x) (h₂ : x ≤ (24797/8192:ℝ)) : (26016381/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (163752449/2000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (423762193/5000000000:ℝ) := by nlinarith
  have hc1 : (124551332387/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (124551332387/125000000000:ℝ) ≤ taylorCos (423762193/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (996650016267/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (163752449/2000000000:ℝ) + taylorErr ≤ (996650016267/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (40892386867/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (40892386867/500000000000:ℝ) ≤ taylorSin (163752449/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (84651014843/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (423762193/5000000000:ℝ) + taylorErr ≤ (84651014843/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-996650016267/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-124551332387/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-84651014843/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-40892386867/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (4753327092661/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9509530399301/1000000000000:ℝ) := by nlinarith
  have hp1 : (1966687398821/125000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3147651906347/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-166532455153/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-80422541959/62500000000:ℝ) := by nlinarith
  have hN : (290110655077/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (8993116841523/50000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (290110655077/1000000000000:ℝ) (8993116841523/50000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (26016381/10000000000000:ℝ) ≤ ((290110655077/1000000000000:ℝ)/(8993116841523/50000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_413 (x : ℝ) (h₁ : (3099/1024:ℝ) ≤ x) (h₂ : x ≤ (24797/8192:ℝ)) : (28822173/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (6626797/80000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (423762193/5000000000:ℝ) := by nlinarith
  have hc1 : (124551332387/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (124551332387/125000000000:ℝ) ≤ taylorCos (423762193/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (124571393507/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (6626797/80000000:ℝ) + taylorErr ≤ (124571393507/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (41370131121/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (41370131121/500000000000:ℝ) ≤ taylorSin (6626797/80000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (84651014843/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (423762193/5000000000:ℝ) + taylorErr ≤ (84651014843/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-124571393507/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-124551332387/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-84651014843/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-41370131121/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1901522584663/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9509530399301/1000000000000:ℝ) := by nlinarith
  have hp1 : (7867542950293/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3147651906347/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-166532455153/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-650962566907/500000000000:ℝ) := by nlinarith
  have hN : (152676992879/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (8993116841523/50000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (152676992879/500000000000:ℝ) (8993116841523/50000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (28822173/10000000000000:ℝ) ≤ ((152676992879/500000000000:ℝ)/(8993116841523/50000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_414 (x : ℝ) (h₁ : (3099/1024:ℝ) ≤ x) (h₂ : x ≤ (49599/16384:ℝ)) : (3601311/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (6626797/80000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (428555883/5000000000:ℝ) := by nlinarith
  have hc1 : (996329043027/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (996329043027/1000000000000:ℝ) ≤ taylorCos (428555883/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (124571393507/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (6626797/80000000:ℝ) + taylorErr ≤ (124571393507/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (41370131121/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (41370131121/500000000000:ℝ) ≤ taylorSin (6626797/80000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (21401568139/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (428555883/5000000000:ℝ) + taylorErr ≤ (21401568139/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-124571393507/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-996329043027/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-21401568139/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-41370131121/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1901522584663/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9510489137293/1000000000000:ℝ) := by nlinarith
  have hp1 : (7867542950293/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15739846241773/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1347429567363/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-650962566907/500000000000:ℝ) := by nlinarith
  have hN : (152676992879/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (179898807261137/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (152676992879/500000000000:ℝ) (179898807261137/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (3601311/1250000000000:ℝ) ≤ ((152676992879/500000000000:ℝ)/(179898807261137/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_415 (x : ℝ) (h₁ : (3099/1024:ℝ) ≤ x) (h₂ : x ≤ (12401/4096:ℝ)) : (28798809/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (6626797/80000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (433349573/5000000000:ℝ) := by nlinarith
  have hc1 : (996246511153/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (996246511153/1000000000000:ℝ) ≤ taylorCos (433349573/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (124571393507/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (6626797/80000000:ℝ) + taylorErr ≤ (124571393507/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (41370131121/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (41370131121/500000000000:ℝ) ≤ taylorSin (6626797/80000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (86561451583/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (433349573/5000000000:ℝ) + taylorErr ≤ (86561451583/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-124571393507/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-996246511153/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-86561451583/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-41370131121/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1901522584663/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1902289575057/200000000000:ℝ) := by nlinarith
  have hp1 : (7867542950293/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15741432951811/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-681300643153/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-650962566907/500000000000:ℝ) := by nlinarith
  have hN : (152676992879/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (11245955085533/62500000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (152676992879/500000000000:ℝ) (11245955085533/62500000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (28798809/10000000000000:ℝ) ≤ ((152676992879/500000000000:ℝ)/(11245955085533/62500000000:ℝ))^2 := by norm_num
  linarith

theorem wc_416 (x : ℝ) (h₁ : (3099/1024:ℝ) ≤ x) (h₂ : x ≤ (24807/8192:ℝ)) : (28775469/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (6626797/80000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (442936953/5000000000:ℝ) := by nlinarith
  have hc1 : (996078700297/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (996078700297/1000000000000:ℝ) ≤ taylorCos (442936953/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (124571393507/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (6626797/80000000:ℝ) + taylorErr ≤ (124571393507/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (41370131121/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (41370131121/500000000000:ℝ) ≤ taylorSin (6626797/80000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (88471570061/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (442936953/5000000000:ℝ) + taylorErr ≤ (88471570061/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-124571393507/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-996078700297/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-88471570061/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-41370131121/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1901522584663/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (951336535127/100000000000:ℝ) := by nlinarith
  have hp1 : (7867542950293/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15744606371889/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-696475022857/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-650962566907/500000000000:ℝ) := by nlinarith
  have hN : (152676992879/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (18000824061349/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (152676992879/500000000000:ℝ) (18000824061349/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (28775469/10000000000000:ℝ) ≤ ((152676992879/500000000000:ℝ)/(18000824061349/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_417 (x : ℝ) (h₁ : (3099/1024:ℝ) ≤ x) (h₂ : x ≤ (6203/2048:ℝ)) : (3594019/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (6626797/80000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (181009733/2000000000:ℝ) := by nlinarith
  have hc1 : (497953613577/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (497953613577/500000000000:ℝ) ≤ taylorCos (181009733/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (124571393507/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (6626797/80000000:ℝ) + taylorErr ≤ (124571393507/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (41370131121/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (41370131121/500000000000:ℝ) ≤ taylorSin (6626797/80000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (18076272631/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (181009733/2000000000:ℝ) + taylorErr ≤ (18076272631/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-124571393507/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-497953613577/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-18076272631/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-41370131121/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1901522584663/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1903056565451/200000000000:ℝ) := by nlinarith
  have hp1 : (7867542950293/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15747779791967/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1423305804263/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-650962566907/500000000000:ℝ) := by nlinarith
  have hN : (152676992879/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (45020303641327/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (152676992879/500000000000:ℝ) (45020303641327/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (3594019/1250000000000:ℝ) ≤ ((152676992879/500000000000:ℝ)/(45020303641327/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_418 (x : ℝ) (h₁ : (3099/1024:ℝ) ≤ x) (h₂ : x ≤ (12411/4096:ℝ)) : (2870559/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (6626797/80000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (188679637/2000000000:ℝ) := by nlinarith
  have hc1 : (995553296499/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (995553296499/1000000000000:ℝ) ≤ taylorCos (188679637/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (124571393507/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (6626797/80000000:ℝ) + taylorErr ≤ (124571393507/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (41370131121/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (41370131121/500000000000:ℝ) ≤ taylorSin (6626797/80000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (47099972801/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (188679637/2000000000:ℝ) + taylorErr ≤ (47099972801/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-124571393507/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-995553296499/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-47099972801/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-41370131121/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1901522584663/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (380764711169/40000000000:ℝ) := by nlinarith
  have hp1 : (7867542950293/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (7877063316061/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1484037871753/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-650962566907/500000000000:ℝ) := by nlinarith
  have hN : (152676992879/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (36045441317903/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (152676992879/500000000000:ℝ) (36045441317903/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2870559/1000000000000:ℝ) ≤ ((152676992879/500000000000:ℝ)/(36045441317903/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_419 (x : ℝ) (h₁ : (3099/1024:ℝ) ≤ x) (h₂ : x ≤ (97/32:ℝ)) : (14329561/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (6626797/80000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (196349541/2000000000:ℝ) := by nlinarith
  have hc1 : (995184724403/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (995184724403/1000000000000:ℝ) ≤ taylorCos (196349541/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (124571393507/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (6626797/80000000:ℝ) + taylorErr ≤ (124571393507/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (41370131121/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (41370131121/500000000000:ℝ) ≤ taylorSin (6626797/80000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (98017142667/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (196349541/2000000000:ℝ) + taylorErr ≤ (98017142667/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-124571393507/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-995184724403/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-98017142667/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-41370131121/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1901522584663/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1904590546239/200000000000:ℝ) := by nlinarith
  have hp1 : (7867542950293/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15760473472277/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-24137446513/15625000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-650962566907/500000000000:ℝ) := by nlinarith
  have hN : (152676992879/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (180373257441149/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (152676992879/500000000000:ℝ) (180373257441149/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (14329561/5000000000000:ℝ) ≤ ((152676992879/500000000000:ℝ)/(180373257441149/1000000000000:ℝ))^2 := by norm_num
  linarith

end Zeta23Ext.Bridge.FourPoint
