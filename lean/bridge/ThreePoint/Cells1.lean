import ThreePoint.Base

noncomputable section
open Real
namespace Zeta23Ext.Bridge.ThreePoint


theorem wc_60 (x : ℝ) (h₁ : (2161/2048:ℝ) ≤ x) (h₂ : x ≤ (541/512:ℝ)) : (1567539/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (173339829/1000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (889708857/5000000000:ℝ) := by nlinarith
  have hc1 : (246052522531/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (246052522531/250000000000:ℝ) ≤ taylorCos (889708857/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (3078169479/3125000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (173339829/1000000000:ℝ) + taylorErr ≤ (3078169479/3125000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (21559135213/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (21559135213/125000000000:ℝ) ≤ taylorSin (173339829/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (177004222679/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (889708857/5000000000:ℝ) + taylorErr ≤ (177004222679/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-3078169479/3125000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-246052522531/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-177004222679/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-21559135213/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (165746624131/50000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (663906884997/200000000000:ℝ) := by nlinarith
  have hp1 : (1371552139043/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5493824837953/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-972430194977/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-946223296553/1000000000000:ℝ) := by nlinarith
  have hN : (11779895147/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (21038617597321/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (11779895147/1000000000000:ℝ) (21038617597321/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1567539/5000000000000:ℝ) ≤ ((11779895147/1000000000000:ℝ)/(21038617597321/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_61 (x : ℝ) (_h₁ : (541/512:ℝ) ≤ x) (_h₂ : x ≤ (1085/1024:ℝ)) : (0:ℝ) ≤ wfun x := wfun_nonneg x

theorem wc_62 (x : ℝ) (_h₁ : (541/512:ℝ) ≤ x) (_h₂ : x ≤ (17/16:ℝ)) : (0:ℝ) ≤ wfun x := wfun_nonneg x

theorem wc_63 (x : ℝ) (h₁ : (1085/1024:ℝ) ≤ x) (h₂ : x ≤ (17/16:ℝ)) : (1243063/312500000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1871456561/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1963495409/10000000000:ℝ) := by nlinarith
  have hc1 : (980785278131/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (980785278131/1000000000000:ℝ) ≤ taylorCos (1963495409/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (491269652277/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1871456561/10000000000:ℝ) + taylorErr ≤ (491269652277/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (9302757469/50000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (9302757469/50000000000:ℝ) ≤ taylorSin (1871456561/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (24386290541/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1963495409/10000000000:ℝ) + taylorErr ≤ (24386290541/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-491269652277/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-980785278131/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-24386290541/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-9302757469/50000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3328738309711/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (83448554861/25000000000:ℝ) := by nlinarith
  have hp1 : (5509057180423/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (690536208837/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-538867731769/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-512494228323/500000000000:ℝ) := by nlinarith
  have hN : (10612288023/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10641858093423/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (10612288023/250000000000:ℝ) (10641858093423/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1243063/312500000000:ℝ) ≤ ((10612288023/250000000000:ℝ)/(10641858093423/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_64 (x : ℝ) (h₁ : (17/16:ℝ) ≤ x) (h₂ : x ≤ (547/512:ℝ)) : (202769189/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/625000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (134223319/625000000:ℝ) := by nlinarith
  have hc1 : (7816225123/8000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (7816225123/8000000000:ℝ) ≤ taylorCos (134223319/625000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (39231411307/40000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/625000000:ℝ) + taylorErr ≤ (39231411307/40000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (97545159853/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (97545159853/500000000000:ℝ) ≤ taylorSin (122718463/625000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (6659697571/31250000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (134223319/625000000:ℝ) + taylorErr ≤ (6659697571/31250000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-39231411307/40000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-7816225123/8000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-6659697571/31250000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-97545159853/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3337942194439/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1678174981947/500000000000:ℝ) := by nlinarith
  have hp1 : (5524289596591/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2777377251719/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-118377552237/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1077735423547/1000000000000:ℝ) := by nlinarith
  have hN : (12118767609/125000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (21530170160263/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (12118767609/125000000000:ℝ) (21530170160263/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (202769189/10000000000000:ℝ) ≤ ((12118767609/125000000000:ℝ)/(21530170160263/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_65 (x : ℝ) (h₁ : (17/16:ℝ) ≤ x) (h₂ : x ≤ (275/256:ℝ)) : (24192/1220703125:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/625000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1165825399/5000000000:ℝ) := by nlinarith
  have hc1 : (486469974967/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (486469974967/500000000000:ℝ) ≤ taylorCos (1165825399/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (39231411307/40000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/625000000:ℝ) + taylorErr ≤ (39231411307/40000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (97545159853/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (97545159853/500000000000:ℝ) ≤ taylorSin (122718463/625000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (231058110583/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1165825399/5000000000:ℝ) + taylorErr ≤ (231058110583/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-39231411307/40000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-486469974967/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-231058110583/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-97545159853/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3337942194439/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3374757733349/1000000000000:ℝ) := by nlinarith
  have hp1 : (5524289596591/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5585219336181/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-129051022701/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1077735423547/1000000000000:ℝ) := by nlinarith
  have hN : (12118767609/125000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10888989758799/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (12118767609/125000000000:ℝ) (10888989758799/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (24192/1220703125:ℝ) ≤ ((12118767609/125000000000:ℝ)/(10888989758799/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_66 (x : ℝ) (h₁ : (17/16:ℝ) ≤ x) (h₂ : x ≤ (139/128:ℝ)) : (189390231/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/625000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (2699806187/10000000000:ℝ) := by nlinarith
  have hc1 : (38551042541/40000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (38551042541/40000000000:ℝ) ≤ taylorCos (2699806187/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (39231411307/40000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/625000000:ℝ) + taylorErr ≤ (39231411307/40000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (97545159853/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (97545159853/500000000000:ℝ) ≤ taylorSin (122718463/625000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (33339094971/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2699806187/10000000000:ℝ) + taylorErr ≤ (33339094971/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-39231411307/40000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-38551042541/40000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-33339094971/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-97545159853/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3337942194439/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1705786636129/500000000000:ℝ) := by nlinarith
  have hp1 : (5524289596591/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5646149001667/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-188237497787/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1077735423547/1000000000000:ℝ) := by nlinarith
  have hN : (12118767609/125000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (22277664383971/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (12118767609/125000000000:ℝ) (22277664383971/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (189390231/10000000000000:ℝ) ≤ ((12118767609/125000000000:ℝ)/(22277664383971/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_67 (x : ℝ) (h₁ : (17/16:ℝ) ≤ x) (h₂ : x ≤ (71/64:ℝ)) : (173234703/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/625000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (687223393/2000000000:ℝ) := by nlinarith
  have hc1 : (235386015729/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (235386015729/250000000000:ℝ) ≤ taylorCos (687223393/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (39231411307/40000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/625000000:ℝ) + taylorErr ≤ (39231411307/40000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (97545159853/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (97545159853/500000000000:ℝ) ≤ taylorSin (122718463/625000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (336889855667/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (687223393/2000000000:ℝ) + taylorErr ≤ (336889855667/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-39231411307/40000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-235386015729/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-336889855667/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-97545159853/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3337942194439/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3485204350077/1000000000000:ℝ) := by nlinarith
  have hp1 : (5524289596591/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5768008332639/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1943183494669/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1077735423547/1000000000000:ℝ) := by nlinarith
  have hN : (12118767609/125000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (2911662340449/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (12118767609/125000000000:ℝ) (2911662340449/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (173234703/10000000000000:ℝ) ≤ ((12118767609/125000000000:ℝ)/(2911662340449/125000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_68 (x : ℝ) (h₁ : (547/512:ℝ) ≤ x) (h₂ : x ≤ (275/256:ℝ)) : (901248747/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2147573103/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1165825399/5000000000:ℝ) := by nlinarith
  have hc1 : (486469974967/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (486469974967/500000000000:ℝ) ≤ taylorCos (1165825399/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (977028144921/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2147573103/10000000000:ℝ) + taylorErr ≤ (977028144921/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (4262206353/20000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (4262206353/20000000000:ℝ) ≤ taylorSin (2147573103/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (231058110583/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1165825399/5000000000:ℝ) + taylorErr ≤ (231058110583/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-977028144921/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-486469974967/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-231058110583/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-4262206353/20000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3356349963893/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3374757733349/1000000000000:ℝ) := by nlinarith
  have hp1 : (1388688607231/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5585219336181/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-129051022701/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-236755096163/200000000000:ℝ) := by nlinarith
  have hN : (103373667947/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10888989758799/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (103373667947/500000000000:ℝ) (10888989758799/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (901248747/10000000000000:ℝ) ≤ ((103373667947/500000000000:ℝ)/(10888989758799/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_69 (x : ℝ) (h₁ : (275/256:ℝ) ≤ x) (h₂ : x ≤ (139/128:ℝ)) : (2032077427/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2331650797/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (2699806187/10000000000:ℝ) := by nlinarith
  have hc1 : (38551042541/40000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (38551042541/40000000000:ℝ) ≤ taylorCos (2699806187/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (972939954481/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2331650797/10000000000:ℝ) + taylorErr ≤ (972939954481/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (231058105961/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (231058105961/1000000000000:ℝ) ≤ taylorSin (2331650797/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (33339094971/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2699806187/10000000000:ℝ) + taylorErr ≤ (33339094971/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-972939954481/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-38551042541/40000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-33339094971/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-231058105961/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (843689433337/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1705786636129/500000000000:ℝ) := by nlinarith
  have hp1 : (5585219261259/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5646149001667/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-188237497787/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1290510183883/1000000000000:ℝ) := by nlinarith
  have hN : (158785114701/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (22277664383971/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (158785114701/500000000000:ℝ) (22277664383971/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2032077427/10000000000000:ℝ) ≤ ((158785114701/500000000000:ℝ)/(22277664383971/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_70 (x : ℝ) (h₁ : (139/128:ℝ) ≤ x) (h₂ : x ≤ (71/64:ℝ)) : (5416703501/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1349903093/5000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (687223393/2000000000:ℝ) := by nlinarith
  have hc1 : (235386015729/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (235386015729/250000000000:ℝ) ≤ taylorCos (687223393/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (240944017019/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1349903093/5000000000:ℝ) + taylorErr ≤ (240944017019/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (266712755147/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (266712755147/1000000000000:ℝ) ≤ taylorSin (1349903093/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (336889855667/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (687223393/2000000000:ℝ) + taylorErr ≤ (336889855667/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-240944017019/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-235386015729/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-336889855667/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-266712755147/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3411573272257/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3485204350077/1000000000000:ℝ) := by nlinarith
  have hp1 : (5646148925927/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5768008332639/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1943183494669/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-376474984001/250000000000:ℝ) := by nlinarith
  have hN : (67765483491/125000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (2911662340449/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (67765483491/125000000000:ℝ) (2911662340449/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (5416703501/10000000000000:ℝ) ≤ ((67765483491/125000000000:ℝ)/(2911662340449/125000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_71 (x : ℝ) (h₁ : (71/64:ℝ) ≤ x) (h₂ : x ≤ (9/8:ℝ)) : (2180450321/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (859029241/2500000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (3926990817/10000000000:ℝ) := by nlinarith
  have hc1 : (923879530249/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (923879530249/1000000000000:ℝ) ≤ taylorCos (3926990817/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (470772033737/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (859029241/2500000000:ℝ) + taylorErr ≤ (470772033737/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (336889851049/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (336889851049/1000000000000:ℝ) ≤ taylorSin (859029241/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (95670858657/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/10000000000:ℝ) + taylorErr ≤ (95670858657/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-470772033737/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-923879530249/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-95670858657/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-336889851049/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (871301087519/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3534291735289/1000000000000:ℝ) := by nlinarith
  have hp1 : (180250257977/31250000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5849247886619/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1119205135621/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-388636688393/200000000000:ℝ) := by nlinarith
  have hN : (1001639374491/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (4796487228053/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1001639374491/1000000000000:ℝ) (4796487228053/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2180450321/1250000000000:ℝ) ≤ ((1001639374491/1000000000000:ℝ)/(4796487228053/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_72 (x : ℝ) (h₁ : (9/8:ℝ) ≤ x) (h₂ : x ≤ (5/4:ℝ)) : (48507697/25000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/312500000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (923879534811/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/312500000:ℝ) + taylorErr ≤ (923879534811/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (95670857503/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (95670857503/250000000000:ℝ) ≤ taylorSin (122718463/312500000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (176776695861/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/5000000000:ℝ) + taylorErr ≤ (176776695861/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-923879534811/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-88388347351/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-176776695861/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-95670857503/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (441786466911/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (981747704247/250000000000:ℝ) := by nlinarith
  have hp1 : (1169849561631/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3249582159233/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-919120635261/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1119205107107/500000000000:ℝ) := by nlinarith
  have hN : (1314530679403/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (29842513753417/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1314530679403/1000000000000:ℝ) (29842513753417/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (48507697/25000000000:ℝ) ≤ ((1314530679403/1000000000000:ℝ)/(29842513753417/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_73 (x : ℝ) (h₁ : (5/4:ℝ) ≤ x) (h₂ : x ≤ (3/2:ℝ)) : (20056696131/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * ((3/2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((3/2:ℝ) - x) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * ((3/2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((3/2:ℝ) - x)) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * ((3/2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((3/2:ℝ) - x)) ≤ (176776695861/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/5000000000:ℝ) + taylorErr ≤ (176776695861/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((3/2:ℝ) - x)) := by
    have h := (trig_shift (3/2:ℝ) (x - (3/2:ℝ))).1
    rw [show (3/2:ℝ) + (x - (3/2:ℝ)) = x by ring, cs_h3.1, cs_h3.2] at h
    rw [h, cos_flip (3/2:ℝ) x, sin_flip (3/2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((3/2:ℝ) - x)) := by
    have h := (trig_shift (3/2:ℝ) (x - (3/2:ℝ))).2
    rw [show (3/2:ℝ) + (x - (3/2:ℝ)) = x by ring, cs_h3.1, cs_h3.2] at h
    rw [h, cos_flip (3/2:ℝ) x, sin_flip (3/2:ℝ) x]; ring
  have hcxl : (-176776695861/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (1131/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-500000001131/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-88388347351/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3926990816987/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (942477796077/200000000000:ℝ) := by nlinarith
  have hp1 : (1624791057821/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3899498591079/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-38994985999/5000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-4595603084527/1000000000000:ℝ) := by nlinarith
  have hN : (3888496301083/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10853304951227/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3888496301083/1000000000000:ℝ) (10853304951227/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (20056696131/2500000000000:ℝ) ≤ ((3888496301083/1000000000000:ℝ)/(10853304951227/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_74 (x : ℝ) (h₁ : (3/2:ℝ) ≤ x) (h₂ : x ≤ (7/4:ℝ)) : (86044756753/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * (x - (3/2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3/2:ℝ)) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3/2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3/2:ℝ))) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3/2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3/2:ℝ))) ≤ (176776695861/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/5000000000:ℝ) + taylorErr ≤ (176776695861/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (3/2:ℝ))) := by
    have h := (trig_shift (3/2:ℝ) (x - (3/2:ℝ))).1
    rw [show (3/2:ℝ) + (x - (3/2:ℝ)) = x by ring, cs_h3.1, cs_h3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3/2:ℝ))) := by
    have h := (trig_shift (3/2:ℝ) (x - (3/2:ℝ))).2
    rw [show (3/2:ℝ) + (x - (3/2:ℝ)) = x by ring, cs_h3.1, cs_h3.2] at h
    rw [h]; ring
  have hcxl : (-1131/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (176776695861/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-500000001131/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-88388347351/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (147262155637/31250000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (5497787143783/1000000000000:ℝ) := by nlinarith
  have hp1 : (389949853877/50000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (9098830045851/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-9098830066433/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-689340462679/125000000000:ℝ) := by nlinarith
  have hN : (551472369917/100000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (14862831739173/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (551472369917/100000000000:ℝ) (14862831739173/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (86044756753/10000000000000:ℝ) ≤ ((551472369917/100000000000:ℝ)/(14862831739173/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_75 (x : ℝ) (h₁ : (7/4:ℝ) ≤ x) (h₂ : x ≤ (15/8:ℝ)) : (1500513453/400000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/312500000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (923879534811/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/312500000:ℝ) + taylorErr ≤ (923879534811/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (95670857503/250000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (95670857503/250000000000:ℝ) ≤ taylorSin (122718463/312500000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (176776695861/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/5000000000:ℝ) + taylorErr ≤ (176776695861/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (923879534811/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-176776695861/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-95670857503/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (2748893571891/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (5890486225481/1000000000000:ℝ) := by nlinarith
  have hp1 : (4549414961899/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (9748746477697/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-861675595557/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1740985722167/500000000000:ℝ) := by nlinarith
  have hN : (2094539111571/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (68395655945163/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2094539111571/500000000000:ℝ) (68395655945163/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1500513453/400000000000:ℝ) ≤ ((2094539111571/500000000000:ℝ)/(68395655945163/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_76 (x : ℝ) (h₁ : (15/8:ℝ) ≤ x) (h₂ : x ≤ (31/16:ℝ)) : (14943341871/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/625000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (3926990817/10000000000:ℝ) := by nlinarith
  have hc1 : (923879530249/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (923879530249/1000000000000:ℝ) ≤ taylorCos (3926990817/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (39231411307/40000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/625000000:ℝ) + taylorErr ≤ (39231411307/40000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (97545159853/500000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (97545159853/500000000000:ℝ) ≤ taylorSin (122718463/625000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (95670858657/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/10000000000:ℝ) + taylorErr ≤ (95670858657/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (923879530249/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (39231411307/40000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-95670858657/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-97545159853/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (147262155637/25000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6086835766331/1000000000000:ℝ) := by nlinarith
  have hp1 : (389949853877/40000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10073704693621/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-120469997237/31250000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-950943020777/500000000000:ℝ) := by nlinarith
  have hN : (2825765571803/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (73099139292573/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2825765571803/1000000000000:ℝ) (73099139292573/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (14943341871/10000000000000:ℝ) ≤ ((2825765571803/1000000000000:ℝ)/(73099139292573/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_77 (x : ℝ) (h₁ : (31/16:ℝ) ≤ x) (h₂ : x ≤ (127/64:ℝ)) : (461990507/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/2500000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (1963495409/10000000000:ℝ) := by nlinarith
  have hc1 : (980785278131/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (980785278131/1000000000000:ℝ) ≤ taylorCos (1963495409/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (249698864617/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/2500000000:ℝ) + taylorErr ≤ (249698864617/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (49067672053/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (49067672053/1000000000000:ℝ) ≤ taylorSin (122718463/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (24386290541/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1963495409/10000000000:ℝ) + taylorErr ≤ (24386290541/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (980785278131/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (249698864617/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-24386290541/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-49067672053/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (608683576633/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (389631120123/62500000000:ℝ) := by nlinarith
  have hp1 : (1007370455849/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10317423355563/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2012829468667/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-247146615817/500000000000:ℝ) := by nlinarith
  have hN : (295015701953/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (19181988450343/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (295015701953/200000000000:ℝ) (19181988450343/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (461990507/1250000000000:ℝ) ≤ ((295015701953/200000000000:ℝ)/(19181988450343/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_78 (x : ℝ) (h₁ : (31/16:ℝ) ≤ x) (h₂ : x ≤ (2:ℝ)) : (158284889/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (1963495409/10000000000:ℝ) := by nlinarith
  have hc1 : (980785278131/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (980785278131/1000000000000:ℝ) ≤ taylorCos (1963495409/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (24386290541/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1963495409/10000000000:ℝ) + taylorErr ≤ (24386290541/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (980785278131/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (500000001131/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-24386290541/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1131/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (608683576633/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (314159265359/50000000000:ℝ) := by nlinarith
  have hp1 : (1007370455849/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10398662909543/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2028678519601/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (11761/500000000000:ℝ) := by nlinarith
  have hN : (980785254609/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (38978417604363/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (980785254609/1000000000000:ℝ) (38978417604363/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (158284889/1000000000000:ℝ) ≤ ((980785254609/1000000000000:ℝ)/(38978417604363/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_79 (x : ℝ) (h₁ : (127/64:ℝ) ≤ x) (h₂ : x ≤ (1019/512:ℝ)) : (725907/2500000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (306796157/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (490873853/10000000000:ℝ) := by nlinarith
  have hc1 : (998795453939/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (998795453939/1000000000000:ℝ) ≤ taylorCos (490873853/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (199905883953/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (306796157/10000000000:ℝ) + taylorErr ≤ (199905883953/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (30674800857/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (30674800857/1000000000000:ℝ) ≤ taylorSin (306796157/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (49067676677/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (490873853/10000000000:ℝ) + taylorErr ≤ (49067676677/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (998795453939/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (199905883953/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-49067676677/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-30674800857/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6234097921967/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3126252845711/500000000000:ℝ) := by nlinarith
  have hp1 : (2579355804291/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2069577637661/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-253873415957/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-316484902543/1000000000000:ℝ) := by nlinarith
  have hN : (657640178241/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (7718765484253/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (657640178241/500000000000:ℝ) (7718765484253/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (725907/2500000000:ℝ) ≤ ((657640178241/500000000000:ℝ)/(7718765484253/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_80 (x : ℝ) (h₁ : (127/64:ℝ) ≤ x) (h₂ : x ≤ (511/256:ℝ)) : (131289511/625000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (490873853/10000000000:ℝ) := by nlinarith
  have hc1 : (998795453939/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (998795453939/1000000000000:ℝ) ≤ taylorCos (490873853/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (999924704101/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/10000000000:ℝ) + taylorErr ≤ (999924704101/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (613576801/50000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (613576801/50000000000:ℝ) ≤ taylorSin (122718463/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (49067676677/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (490873853/10000000000:ℝ) + taylorErr ≤ (49067676677/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (998795453939/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999924704101/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-49067676677/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-613576801/50000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6234097921967/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6270913460877/1000000000000:ℝ) := by nlinarith
  have hp1 : (2579355804291/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1297294127631/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-509241670477/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-126610630643/1000000000000:ℝ) := by nlinarith
  have hN : (562703042291/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (77648711267617/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (562703042291/500000000000:ℝ) (77648711267617/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (131289511/625000000000:ℝ) ≤ ((562703042291/500000000000:ℝ)/(77648711267617/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_81 (x : ℝ) (h₁ : (127/64:ℝ) ≤ x) (h₂ : x ≤ (2:ℝ)) : (410378597/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (490873853/10000000000:ℝ) := by nlinarith
  have hc1 : (998795453939/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (998795453939/1000000000000:ℝ) ≤ taylorCos (490873853/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (49067676677/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (490873853/10000000000:ℝ) + taylorErr ≤ (49067676677/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (998795453939/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (500000001131/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-49067676677/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1131/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6234097921967/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (314159265359/50000000000:ℝ) := by nlinarith
  have hp1 : (2579355804291/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10398662909543/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-510238229519/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (11761/500000000000:ℝ) := by nlinarith
  have hN : (998795430417/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (38978417604363/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (998795430417/1000000000000:ℝ) (38978417604363/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (410378597/2500000000000:ℝ) ≤ ((998795430417/1000000000000:ℝ)/(38978417604363/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_82 (x : ℝ) (h₁ : (1019/512:ℝ) ≤ x) (h₂ : x ≤ (2041/1024:ℝ)) : (2490428543/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (21475731/1000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (153398079/5000000000:ℝ) := by nlinarith
  have hc1 : (499764707619/500000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (499764707619/500000000000:ℝ) ≤ taylorCos (153398079/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (499884703807/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (21475731/1000000000:ℝ) + taylorErr ≤ (499884703807/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (21474077983/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (21474077983/1000000000000:ℝ) ≤ taylorSin (21475731/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (30674805481/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (153398079/5000000000:ℝ) + taylorErr ≤ (30674805481/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (499764707619/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (499884703807/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-30674805481/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-21474077983/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6252505691421/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (125234191523/20000000000:ℝ) := by nlinarith
  have hp1 : (10347888049497/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10363120604677/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-12715468349/40000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-111105677467/500000000000:ℝ) := by nlinarith
  have hN : (305435192543/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (38709006816049/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (305435192543/250000000000:ℝ) (38709006816049/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2490428543/10000000000000:ℝ) ≤ ((305435192543/250000000000:ℝ)/(38709006816049/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_83 (x : ℝ) (h₁ : (1019/512:ℝ) ≤ x) (h₂ : x ≤ (511/256:ℝ)) : (2104769793/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (153398079/5000000000:ℝ) := by nlinarith
  have hc1 : (499764707619/500000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (499764707619/500000000000:ℝ) ≤ taylorCos (153398079/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (999924704101/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/10000000000:ℝ) + taylorErr ≤ (999924704101/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (613576801/50000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (613576801/50000000000:ℝ) ≤ taylorSin (122718463/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (30674805481/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (153398079/5000000000:ℝ) + taylorErr ≤ (30674805481/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (499764707619/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999924704101/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-30674805481/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-613576801/50000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6252505691421/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6270913460877/1000000000000:ℝ) := by nlinarith
  have hp1 : (10347888049497/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1297294127631/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-159176980067/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-12698448093/100000000000:ℝ) := by nlinarith
  have hN : (140814237021/125000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (77648711267617/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (140814237021/125000000000:ℝ) (77648711267617/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2104769793/10000000000000:ℝ) ≤ ((140814237021/125000000000:ℝ)/(77648711267617/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_84 (x : ℝ) (h₁ : (2041/1024:ℝ) ≤ x) (h₂ : x ≤ (4085/2048:ℝ)) : (2295210877/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (84368943/5000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (214757311/10000000000:ℝ) := by nlinarith
  have hc1 : (62485587693/62500000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (62485587693/62500000000:ℝ) ≤ taylorCos (214757311/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (999857643269/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (84368943/5000000000:ℝ) + taylorErr ≤ (999857643269/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (8436492809/500000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (8436492809/500000000000:ℝ) ≤ taylorSin (84368943/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (999857643269/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-21474082607/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-8436492809/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6261709576149/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6266311518513/1000000000000:ℝ) := by nlinarith
  have hp1 : (2072624093133/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5185368406431/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-44540411803/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-87428391287/500000000000:ℝ) := by nlinarith
  have hN : (587313092831/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (38766660047049/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (587313092831/500000000000:ℝ) (38766660047049/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2295210877/10000000000000:ℝ) ≤ ((587313092831/500000000000:ℝ)/(38766660047049/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_85 (x : ℝ) (h₁ : (2041/1024:ℝ) ≤ x) (h₂ : x ≤ (511/256:ℝ)) : (2106365377/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (214757311/10000000000:ℝ) := by nlinarith
  have hc1 : (62485587693/62500000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (62485587693/62500000000:ℝ) ≤ taylorCos (214757311/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (999924704101/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/10000000000:ℝ) + taylorErr ≤ (999924704101/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (613576801/50000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (613576801/50000000000:ℝ) ≤ taylorSin (122718463/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (999924704101/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-21474082607/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-613576801/50000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6261709576149/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6270913460877/1000000000000:ℝ) := by nlinarith
  have hp1 : (2072624093133/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1297294127631/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-222865610099/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-63585703037/500000000000:ℝ) := by nlinarith
  have hN : (563470404581/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (77648711267617/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (563470404581/500000000000:ℝ) (77648711267617/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2106365377/10000000000000:ℝ) ≤ ((563470404581/500000000000:ℝ)/(77648711267617/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_86 (x : ℝ) (h₁ : (4085/2048:ℝ) ≤ x) (h₂ : x ≤ (511/256:ℝ)) : (131690291/625000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (168737887/10000000000:ℝ) := by nlinarith
  have hc1 : (999857638743/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (999857638743/1000000000000:ℝ) ≤ taylorCos (168737887/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (999924704101/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/10000000000:ℝ) + taylorErr ≤ (999924704101/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (613576801/50000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (613576801/50000000000:ℝ) ≤ taylorSin (122718463/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (16872990243/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (168737887/10000000000:ℝ) + taylorErr ≤ (16872990243/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (999857638743/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999924704101/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-16872990243/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-613576801/50000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (391644469907/62500000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6270913460877/1000000000000:ℝ) := by nlinarith
  have hp1 : (10370736673747/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1297294127631/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-175113849263/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-25452973729/200000000000:ℝ) := by nlinarith
  have hN : (281780626847/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (77648711267617/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (281780626847/250000000000:ℝ) (77648711267617/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (131690291/625000000000:ℝ) ≤ ((281780626847/250000000000:ℝ)/(77648711267617/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_87 (x : ℝ) (h₁ : (511/256:ℝ) ≤ x) (h₂ : x ≤ (8179/4096:ℝ)) : (1008150283/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (99708751/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (479369/39062500:ℝ) := by nlinarith
  have hc1 : (124990587447/125000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (124990587447/125000000000:ℝ) ≤ taylorCos (479369/39062500:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (999950293499/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (99708751/10000000000:ℝ) + taylorErr ≤ (999950293499/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (1246338453/125000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (1246338453/125000000000:ℝ) ≤ taylorSin (99708751/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (2454308129/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (479369/39062500:ℝ) + taylorErr ≤ (2454308129/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (124990587447/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999950293499/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-2454308129/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-1246338453/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1567728365219/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6273214432059/1000000000000:ℝ) := by nlinarith
  have hp1 : (10378352881831/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5191080562571/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-127405112231/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-103479522203/1000000000000:ℝ) := by nlinarith
  have hN : (1103404221779/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (77706438621187/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1103404221779/1000000000000:ℝ) (77706438621187/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1008150283/5000000000000:ℝ) ≤ ((1103404221779/1000000000000:ℝ)/(77706438621187/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_88 (x : ℝ) (h₁ : (511/256:ℝ) ≤ x) (h₂ : x ≤ (4091/2048:ℝ)) : (15416863/80000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (76699039/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (479369/39062500:ℝ) := by nlinarith
  have hc1 : (124990587447/125000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (124990587447/125000000000:ℝ) ≤ taylorCos (479369/39062500:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (999970588693/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (76699039/10000000000:ℝ) + taylorErr ≤ (999970588693/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (3834913219/500000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (3834913219/500000000000:ℝ) ≤ taylorSin (76699039/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (2454308129/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (479369/39062500:ℝ) + taylorErr ≤ (2454308129/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (124990587447/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999970588693/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-2454308129/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-3834913219/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1567728365219/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6275515403241/1000000000000:ℝ) := by nlinarith
  have hp1 : (10378352881831/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2077193845847/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-25490368707/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-15920033063/200000000000:ℝ) := by nlinarith
  have hN : (1079524864891/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (77764187152631/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1079524864891/1000000000000:ℝ) (77764187152631/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (15416863/80000000000:ℝ) ≤ ((1079524864891/1000000000000:ℝ)/(77764187152631/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_89 (x : ℝ) (h₁ : (511/256:ℝ) ≤ x) (h₂ : x ≤ (2047/1024:ℝ)) : (877571531/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (6135923/2000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (479369/39062500:ℝ) := by nlinarith
  have hc1 : (124990587447/125000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (124990587447/125000000000:ℝ) ≤ taylorCos (479369/39062500:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (124999412009/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (6135923/2000000000:ℝ) + taylorErr ≤ (124999412009/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (122718177/40000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (122718177/40000000000:ℝ) ≤ taylorSin (6135923/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (2454308129/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (479369/39062500:ℝ) + taylorErr ≤ (2454308129/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (124990587447/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (124999412009/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-2454308129/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-122718177/40000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1567728365219/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1570029336401/250000000000:ℝ) := by nlinarith
  have hp1 : (10378352881831/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10393585437419/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-127545306143/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1990019603/62500000000:ℝ) := by nlinarith
  have hN : (128970626653/125000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (77879747749113/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (128970626653/125000000000:ℝ) (77879747749113/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (877571531/5000000000000:ℝ) ≤ ((128970626653/125000000000:ℝ)/(77879747749113/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_90 (x : ℝ) (h₁ : (511/256:ℝ) ≤ x) (h₂ : x ≤ (2:ℝ)) : (1645228303/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (479369/39062500:ℝ) := by nlinarith
  have hc1 : (124990587447/125000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (124990587447/125000000000:ℝ) ≤ taylorCos (479369/39062500:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (2454308129/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (479369/39062500:ℝ) + taylorErr ≤ (2454308129/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (124990587447/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (500000001131/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-2454308129/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1131/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1567728365219/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (314159265359/50000000000:ℝ) := by nlinarith
  have hp1 : (10378352881831/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10398662909543/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-127607614549/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (11761/500000000000:ℝ) := by nlinarith
  have hN : (499962338027/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (38978417604363/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (499962338027/500000000000:ℝ) (38978417604363/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1645228303/10000000000000:ℝ) ≤ ((499962338027/500000000000:ℝ)/(38978417604363/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_91 (x : ℝ) (h₁ : (8179/4096:ℝ) ≤ x) (h₂ : x ≤ (4091/2048:ℝ)) : (1927303521/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (76699039/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (6231797/625000000:ℝ) := by nlinarith
  have hc1 : (499975144487/500000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (499975144487/500000000000:ℝ) ≤ taylorCos (6231797/625000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (999970588693/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (76699039/10000000000:ℝ) + taylorErr ≤ (999970588693/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (3834913219/500000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (3834913219/500000000000:ℝ) ≤ taylorSin (76699039/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (1246339031/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (6231797/625000000:ℝ) + taylorErr ≤ (1246339031/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (499975144487/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999970588693/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-1246339031/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-3834913219/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3136607216029/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6275515403241/1000000000000:ℝ) := by nlinarith
  have hp1 : (10382160985873/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2077193845847/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-51777755301/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-79629372813/1000000000000:ℝ) := by nlinarith
  have hN : (1079579661787/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (77764187152631/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1079579661787/1000000000000:ℝ) (77764187152631/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1927303521/10000000000000:ℝ) ≤ ((1079579661787/1000000000000:ℝ)/(77764187152631/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_92 (x : ℝ) (h₁ : (4091/2048:ℝ) ≤ x) (h₂ : x ≤ (8185/4096:ℝ)) : (1840360753/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (53689327/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (479369/62500000:ℝ) := by nlinarith
  have hc1 : (124996323021/125000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (124996323021/125000000000:ℝ) ≤ taylorCos (479369/62500000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (499992794789/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (53689327/10000000000:ℝ) + taylorErr ≤ (499992794789/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (1342226161/250000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (1342226161/250000000000:ℝ) ≤ taylorSin (53689327/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (3834915531/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (479369/62500000:ℝ) + taylorErr ≤ (3834915531/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (124996323021/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (499992794789/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-3834915531/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-1342226161/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (156887885081/25000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3138908187211/500000000000:ℝ) := by nlinarith
  have hp1 : (2596492272479/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5194888666663/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-79687836919/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-55761277679/1000000000000:ℝ) := by nlinarith
  have hN : (1055731861847/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (38910978430961/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1055731861847/1000000000000:ℝ) (38910978430961/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1840360753/10000000000000:ℝ) ≤ ((1055731861847/1000000000000:ℝ)/(38910978430961/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_93 (x : ℝ) (h₁ : (4091/2048:ℝ) ≤ x) (h₂ : x ≤ (2047/1024:ℝ)) : (70215147/400000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (6135923/2000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (479369/62500000:ℝ) := by nlinarith
  have hc1 : (124996323021/125000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (124996323021/125000000000:ℝ) ≤ taylorCos (479369/62500000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (124999412009/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (6135923/2000000000:ℝ) + taylorErr ≤ (124999412009/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (122718177/40000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (122718177/40000000000:ℝ) ≤ taylorSin (6135923/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (3834915531/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (479369/62500000:ℝ) + taylorErr ≤ (3834915531/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (124996323021/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (124999412009/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-3834915531/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-122718177/40000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (156887885081/25000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1570029336401/250000000000:ℝ) := by nlinarith
  have hp1 : (2596492272479/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10393585437419/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-39858522217/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-31863679827/1000000000000:ℝ) := by nlinarith
  have hN : (206366852799/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (77879747749113/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (206366852799/200000000000:ℝ) (77879747749113/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (70215147/400000000000:ℝ) ≤ ((206366852799/200000000000:ℝ)/(77879747749113/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_94 (x : ℝ) (h₁ : (8185/4096:ℝ) ≤ x) (h₂ : x ≤ (2047/1024:ℝ)) : (1755469467/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (6135923/2000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (3355583/625000000:ℝ) := by nlinarith
  have hc1 : (999985585053/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (999985585053/1000000000000:ℝ) ≤ taylorCos (3355583/625000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (124999412009/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (6135923/2000000000:ℝ) + taylorErr ≤ (124999412009/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (122718177/40000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (122718177/40000000000:ℝ) ≤ taylorSin (6135923/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (5368909269/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3355583/625000000:ℝ) + taylorErr ≤ (5368909269/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (999985585053/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (124999412009/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-5368909269/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-122718177/40000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6277816374421/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1570029336401/250000000000:ℝ) := by nlinarith
  have hp1 : (2597444298489/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10393585437419/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-27901108597/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-7968840729/250000000000:ℝ) := by nlinarith
  have hN : (1031860947969/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (77879747749113/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1031860947969/1000000000000:ℝ) (77879747749113/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1755469467/10000000000000:ℝ) ≤ ((1031860947969/1000000000000:ℝ)/(77879747749113/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_95 (x : ℝ) (h₁ : (2047/1024:ℝ) ≤ x) (h₂ : x ≤ (16379/8192:ℝ)) : (856909301/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (19174759/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (479369/156250000:ℝ) := by nlinarith
  have hc1 : (999995291547/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (999995291547/1000000000000:ℝ) ≤ taylorCos (479369/156250000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (499999081953/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (19174759/10000000000:ℝ) + taylorErr ≤ (499999081953/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (1917472463/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (1917472463/1000000000000:ℝ) ≤ taylorSin (19174759/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (3067959049/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (479369/156250000:ℝ) + taylorErr ≤ (3067959049/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (999995291547/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (499999081953/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-3067959049/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-1917472463/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6280117345603/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1256253566239/200000000000:ℝ) := by nlinarith
  have hp1 : (5196792648999/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5197744744733/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1993308503/62500000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-24911767/1250000000:ℝ) := by nlinarith
  have hN : (1019924705147/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (77908651134411/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1019924705147/1000000000000:ℝ) (77908651134411/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (856909301/5000000000000:ℝ) ≤ ((1019924705147/1000000000000:ℝ)/(77908651134411/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_96 (x : ℝ) (h₁ : (2047/1024:ℝ) ≤ x) (h₂ : x ≤ (8191/4096:ℝ)) : (104539177/625000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (7669903/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (479369/156250000:ℝ) := by nlinarith
  have hc1 : (999995291547/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (999995291547/1000000000000:ℝ) ≤ taylorCos (479369/156250000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (1599999533/1600000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (7669903/10000000000:ℝ) + taylorErr ≤ (1599999533/1600000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (766987963/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (766987963/1000000000000:ℝ) ≤ taylorSin (7669903/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (3067959049/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (479369/156250000:ℝ) + taylorErr ≤ (3067959049/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (999995291547/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (1599999533/1600000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-3067959049/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-766987963/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6280117345603/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3141209158393/500000000000:ℝ) := by nlinarith
  have hp1 : (5196792648999/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1299674192689/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-15949388801/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1594350963/200000000000:ℝ) := by nlinarith
  have hN : (503983523181/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (77937559814177/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (503983523181/500000000000:ℝ) (77937559814177/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (104539177/625000000000:ℝ) ≤ ((503983523181/500000000000:ℝ)/(77937559814177/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_97 (x : ℝ) (h₁ : (2047/1024:ℝ) ≤ x) (h₂ : x ≤ (2:ℝ)) : (1645460609/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (479369/156250000:ℝ) := by nlinarith
  have hc1 : (999995291547/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (999995291547/1000000000000:ℝ) ≤ taylorCos (479369/156250000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (3067959049/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (479369/156250000:ℝ) + taylorErr ≤ (3067959049/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (999995291547/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (500000001131/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-3067959049/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1131/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6280117345603/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (314159265359/50000000000:ℝ) := by nlinarith
  have hp1 : (5196792648999/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10398662909543/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-31902671971/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (11761/500000000000:ℝ) := by nlinarith
  have hN : (39999810721/40000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (38978417604363/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (39999810721/40000000000:ℝ) (38978417604363/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1645460609/10000000000000:ℝ) ≤ ((39999810721/40000000000:ℝ)/(38978417604363/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_98 (x : ℝ) (h₁ : (16379/8192:ℝ) ≤ x) (h₂ : x ≤ (8191/4096:ℝ)) : (1672641197/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (7669903/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (479369/250000000:ℝ) := by nlinarith
  have hc1 : (999998159381/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (999998159381/1000000000000:ℝ) ≤ taylorCos (479369/250000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (1599999533/1600000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (7669903/10000000000:ℝ) + taylorErr ≤ (1599999533/1600000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (766987963/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (766987963/1000000000000:ℝ) ≤ taylorSin (7669903/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (1917477087/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (479369/250000000:ℝ) + taylorErr ≤ (1917477087/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (999998159381/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (1599999533/1600000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-1917477087/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-766987963/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3140633915597/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3141209158393/500000000000:ℝ) := by nlinarith
  have hp1 : (10395489350019/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1299674192689/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-19936763881/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-9966519/1250000000:ℝ) := by nlinarith
  have hN : (1007971374581/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (77937559814177/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1007971374581/1000000000000:ℝ) (77937559814177/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1672641197/10000000000000:ℝ) ≤ ((1007971374581/1000000000000:ℝ)/(77937559814177/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_99 (x : ℝ) (h₁ : (8191/4096:ℝ) ≤ x) (h₂ : x ≤ (2:ℝ)) : (205684391/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (479369/625000000:ℝ) := by nlinarith
  have hc1 : (999999703601/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (999999703601/1000000000000:ℝ) ≤ taylorCos (479369/625000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (766992587/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (479369/625000000:ℝ) + taylorErr ≤ (766992587/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (999999703601/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (500000001131/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-766992587/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1131/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1256483663357/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (314159265359/50000000000:ℝ) := by nlinarith
  have hp1 : (259934835051/25000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10398662909543/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-7975697367/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (11761/500000000000:ℝ) := by nlinarith
  have hN : (999999680079/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (38978417604363/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (999999680079/1000000000000:ℝ) (38978417604363/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (205684391/1250000000000:ℝ) ≤ ((999999680079/1000000000000:ℝ)/(38978417604363/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_100 (x : ℝ) (h₁ : (2:ℝ) ≤ x) (h₂ : x ≤ (16385/8192:ℝ)) : (203996733/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (479369/1250000000:ℝ) := by nlinarith
  have hc1 : (249999981051/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (249999981051/250000000000:ℝ) ≤ taylorCos (479369/1250000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (383497453/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (479369/1250000000:ℝ) + taylorErr ≤ (383497453/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (249999981051/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (500000001131/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (383497453/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6283185307179/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6283568802377/1000000000000:ℝ) := by nlinarith
  have hp1 : (5199331385027/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10399297593559/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-5881/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (3988104141/1000000000000:ℝ) := by nlinarith
  have hN : (996011820063/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (19491618447103/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (996011820063/1000000000000:ℝ) (19491618447103/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (203996733/1250000000000:ℝ) ≤ ((996011820063/1000000000000:ℝ)/(19491618447103/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_101 (x : ℝ) (h₁ : (2:ℝ) ≤ x) (h₂ : x ≤ (4097/2048:ℝ)) : (1591808227/10000000000000:ℝ) ≤ wfun x := by
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

theorem wc_102 (x : ℝ) (h₁ : (2:ℝ) ≤ x) (h₂ : x ≤ (1025/512:ℝ)) : (1436255057/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (479369/78125000:ℝ) := by nlinarith
  have hc1 : (49999058651/50000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (49999058651/50000000000:ℝ) ≤ taylorCos (479369/78125000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (76698587/12500000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (479369/78125000:ℝ) + taylorErr ≤ (76698587/12500000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (49999058651/50000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (500000001131/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (76698587/12500000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6283185307179/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1572330307583/250000000000:ℝ) := by nlinarith
  have hp1 : (5199331385027/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (325275557931/31250000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-4709/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (63867329739/1000000000000:ℝ) := by nlinarith
  have hN : (936113843281/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (7811112307661/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (936113843281/1000000000000:ℝ) (7811112307661/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1436255057/10000000000000:ℝ) ≤ ((936113843281/1000000000000:ℝ)/(7811112307661/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_103 (x : ℝ) (h₁ : (2:ℝ) ≤ x) (h₂ : x ≤ (257/128:ℝ)) : (179073511/2000000000000:ℝ) ≤ wfun x := by
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

theorem wc_104 (x : ℝ) (_h₁ : (2:ℝ) ≤ x) (_h₂ : x ≤ (65/32:ℝ)) : (0:ℝ) ≤ wfun x := wfun_nonneg x

theorem wc_105 (x : ℝ) (h₁ : (16385/8192:ℝ) ≤ x) (h₂ : x ≤ (4097/2048:ℝ)) : (1591808227/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (3834951/10000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (479369/312500000:ℝ) := by nlinarith
  have hc1 : (99999882119/100000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (99999882119/100000000000:ℝ) ≤ taylorCos (479369/312500000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (124999991091/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (3834951/10000000000:ℝ) + taylorErr ≤ (124999991091/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (95873207/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (95873207/250000000000:ℝ) ≤ taylorSin (3834951/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (124999991091/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (95873207/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1533982461/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (785446100297/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (196397477749/31250000000:ℝ) := by nlinarith
  have hp1 : (10399297454061/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5200600822803/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (3988055989/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (7977630449/500000000000:ℝ) := by nlinarith
  have hN : (246010890073/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (15599078611423/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (246010890073/250000000000:ℝ) (15599078611423/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1591808227/10000000000000:ℝ) ≤ ((246010890073/250000000000:ℝ)/(15599078611423/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_106 (x : ℝ) (h₁ : (4097/2048:ℝ) ≤ x) (h₂ : x ≤ (16391/8192:ℝ)) : (1552153897/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (15339807/10000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (3355583/1250000000:ℝ) := by nlinarith
  have hc1 : (3124988733/3125000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (3124988733/3125000000:ℝ) ≤ taylorCos (3355583/1250000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (499999412857/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (15339807/10000000000:ℝ) + taylorErr ≤ (499999412857/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (383494459/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (383494459/250000000000:ℝ) ≤ taylorSin (15339807/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (1342232719/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3355583/1250000000:ℝ) + taylorErr ≤ (1342232719/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (3124988733/3125000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (499999412857/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (383494459/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1342232719/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6284719287967/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6285869773559/1000000000000:ℝ) := by nlinarith
  have hp1 : (5200600753041/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2600776424413/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (7977606289/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (13963388847/500000000000:ℝ) := by nlinarith
  have hN : (486034808433/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (39012158810143/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (486034808433/500000000000:ℝ) (39012158810143/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1552153897/10000000000000:ℝ) ≤ ((486034808433/500000000000:ℝ)/(39012158810143/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_107 (x : ℝ) (h₁ : (4097/2048:ℝ) ≤ x) (h₂ : x ≤ (8197/4096:ℝ)) : (302602101/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (15339807/10000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (479369/125000000:ℝ) := by nlinarith
  have hc1 : (499996322159/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (499996322159/500000000000:ℝ) ≤ taylorCos (479369/125000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (499999412857/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (15339807/10000000000:ℝ) + taylorErr ≤ (499999412857/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (383494459/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (383494459/250000000000:ℝ) ≤ taylorSin (15339807/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (1917472431/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (479369/125000000:ℝ) + taylorErr ≤ (1917472431/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (499996322159/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (499999412857/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (383494459/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1917472431/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6284719287967/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (125740405183/20000000000:ℝ) := by nlinarith
  have hp1 : (5200600753041/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10405009749699/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (7977606289/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (39902638679/1000000000000:ℝ) := by nlinarith
  have hN : (960090005639/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (39026623738963/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (960090005639/1000000000000:ℝ) (39026623738963/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (302602101/2000000000000:ℝ) ≤ ((960090005639/1000000000000:ℝ)/(39026623738963/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_108 (x : ℝ) (h₁ : (4097/2048:ℝ) ≤ x) (h₂ : x ≤ (1025/512:ℝ)) : (1436255057/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (15339807/10000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (479369/78125000:ℝ) := by nlinarith
  have hc1 : (49999058651/50000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (49999058651/50000000000:ℝ) ≤ taylorCos (479369/78125000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (499999412857/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (15339807/10000000000:ℝ) + taylorErr ≤ (499999412857/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (383494459/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (383494459/250000000000:ℝ) ≤ taylorSin (15339807/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (76698587/12500000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (479369/78125000:ℝ) + taylorErr ≤ (76698587/12500000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (49999058651/50000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (499999412857/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (383494459/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (76698587/12500000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6284719287967/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1572330307583/250000000000:ℝ) := by nlinarith
  have hp1 : (5200600753041/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (325275557931/31250000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (7977606289/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (63867329739/1000000000000:ℝ) := by nlinarith
  have hN : (936113843281/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (7811112307661/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (936113843281/1000000000000:ℝ) (7811112307661/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1436255057/10000000000000:ℝ) ≤ ((936113843281/1000000000000:ℝ)/(7811112307661/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_109 (x : ℝ) (h₁ : (16391/8192:ℝ) ≤ x) (h₂ : x ≤ (8197/4096:ℝ)) : (302602101/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (26844663/10000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (479369/125000000:ℝ) := by nlinarith
  have hc1 : (499996322159/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (499996322159/500000000000:ℝ) ≤ taylorCos (479369/125000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (199999279817/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (26844663/10000000000:ℝ) + taylorErr ≤ (199999279817/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (1342230407/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (1342230407/500000000000:ℝ) ≤ taylorSin (26844663/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (1917472431/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (479369/125000000:ℝ) + taylorErr ≤ (1917472431/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (499996322159/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (199999279817/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (1342230407/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1917472431/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3142934886779/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (125740405183/20000000000:ℝ) := by nlinarith
  have hp1 : (10403105558103/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10405009749699/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (13963364607/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (39902638679/1000000000000:ℝ) := by nlinarith
  have hN : (960090005639/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (39026623738963/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (960090005639/1000000000000:ℝ) (39026623738963/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (302602101/2000000000000:ℝ) ≤ ((960090005639/1000000000000:ℝ)/(39026623738963/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_110 (x : ℝ) (h₁ : (8197/4096:ℝ) ≤ x) (h₂ : x ≤ (16397/8192:ℝ)) : (1474377683/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (38349519/10000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (6231797/1250000000:ℝ) := by nlinarith
  have hc1 : (99998757047/100000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (99998757047/100000000000:ℝ) ≤ taylorCos (6231797/1250000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (999992648843/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (38349519/10000000000:ℝ) + taylorErr ≤ (999992648843/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (1917470119/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (1917470119/500000000000:ℝ) ≤ taylorSin (38349519/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (498541921/100000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (6231797/1250000000:ℝ) + taylorErr ≤ (498541921/100000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (99998757047/100000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999992648843/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (1917470119/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (498541921/100000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6287020259149/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6288170744741/1000000000000:ℝ) := by nlinarith
  have hp1 : (2601252402531/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2081382760349/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (3990259003/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (10376565597/200000000000:ℝ) := by nlinarith
  have hN : (189620948497/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (39041091315017/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (189620948497/200000000000:ℝ) (39041091315017/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1474377683/10000000000000:ℝ) ≤ ((189620948497/200000000000:ℝ)/(39041091315017/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_111 (x : ℝ) (h₁ : (8197/4096:ℝ) ≤ x) (h₂ : x ≤ (1025/512:ℝ)) : (1436255057/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (38349519/10000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (479369/78125000:ℝ) := by nlinarith
  have hc1 : (49999058651/50000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (49999058651/50000000000:ℝ) ≤ taylorCos (479369/78125000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (999992648843/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (38349519/10000000000:ℝ) + taylorErr ≤ (999992648843/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (1917470119/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (1917470119/500000000000:ℝ) ≤ taylorSin (38349519/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (76698587/12500000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (479369/78125000:ℝ) + taylorErr ≤ (76698587/12500000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (49999058651/50000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999992648843/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (1917470119/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (76698587/12500000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6287020259149/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1572330307583/250000000000:ℝ) := by nlinarith
  have hp1 : (2601252402531/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (325275557931/31250000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (3990259003/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (63867329739/1000000000000:ℝ) := by nlinarith
  have hN : (936113843281/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (7811112307661/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (936113843281/1000000000000:ℝ) (7811112307661/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1436255057/10000000000000:ℝ) ≤ ((936113843281/1000000000000:ℝ)/(7811112307661/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_112 (x : ℝ) (h₁ : (16397/8192:ℝ) ≤ x) (h₂ : x ≤ (1025/512:ℝ)) : (1436255057/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (79767/16000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (479369/78125000:ℝ) := by nlinarith
  have hc1 : (49999058651/50000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (49999058651/50000000000:ℝ) ≤ taylorCos (479369/78125000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (499993787497/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (79767/16000000:ℝ) + taylorErr ≤ (499993787497/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (2492707293/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (2492707293/500000000000:ℝ) ≤ taylorSin (79767/16000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (76698587/12500000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (479369/78125000:ℝ) + taylorErr ≤ (76698587/12500000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (49999058651/50000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (499993787497/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (2492707293/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (76698587/12500000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (314408537237/50000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1572330307583/250000000000:ℝ) := by nlinarith
  have hp1 : (2081382732429/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (325275557931/31250000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (25941389583/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (63867329739/1000000000000:ℝ) := by nlinarith
  have hN : (936113843281/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (7811112307661/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (936113843281/1000000000000:ℝ) (7811112307661/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1436255057/10000000000000:ℝ) ≤ ((936113843281/1000000000000:ℝ)/(7811112307661/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_113 (x : ℝ) (h₁ : (1025/512:ℝ) ≤ x) (h₂ : x ≤ (16403/8192:ℝ)) : (279728451/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (61359231/10000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (9108011/1250000000:ℝ) := by nlinarith
  have hc1 : (999973451979/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (999973451979/1000000000000:ℝ) ≤ taylorCos (9108011/1250000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (199996235509/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (61359231/10000000000:ℝ) + taylorErr ≤ (199996235509/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (1227176467/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (1227176467/200000000000:ℝ) ≤ taylorSin (61359231/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (1821586647/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (9108011/1250000000:ℝ) + taylorErr ≤ (1821586647/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (999973451979/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (199996235509/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (1227176467/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1821586647/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6289321230331/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6290471715923/1000000000000:ℝ) := by nlinarith
  have hp1 : (5204408857083/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5205360952919/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (3193364037/50000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (37928064019/500000000000:ℝ) := by nlinarith
  have hN : (924117323941/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (15628013763531/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (924117323941/1000000000000:ℝ) (15628013763531/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (279728451/2000000000000:ℝ) ≤ ((924117323941/1000000000000:ℝ)/(15628013763531/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_114 (x : ℝ) (h₁ : (1025/512:ℝ) ≤ x) (h₂ : x ≤ (8203/4096:ℝ)) : (1361538899/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (61359231/10000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (5273059/625000000:ℝ) := by nlinarith
  have hc1 : (199992881471/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (199992881471/200000000000:ℝ) ≤ taylorCos (5273059/625000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (199996235509/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (61359231/10000000000:ℝ) + taylorErr ≤ (199996235509/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (1227176467/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (1227176467/200000000000:ℝ) ≤ taylorSin (61359231/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (8436796571/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (5273059/625000000:ℝ) + taylorErr ≤ (8436796571/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (199992881471/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (199996235509/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (1227176467/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (8436796571/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6289321230331/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6291622201513/1000000000000:ℝ) := by nlinarith
  have hp1 : (5204408857083/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10412625957883/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (3193364037/50000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (87849206977/1000000000000:ℝ) := by nlinarith
  have hN : (456057600189/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (78169019853143/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (456057600189/500000000000:ℝ) (78169019853143/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1361538899/10000000000000:ℝ) ≤ ((456057600189/500000000000:ℝ)/(78169019853143/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_115 (x : ℝ) (h₁ : (1025/512:ℝ) ≤ x) (h₂ : x ≤ (4103/2048:ℝ)) : (10069211/78125000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (61359231/10000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (3355583/312500000:ℝ) := by nlinarith
  have hc1 : (999942347413/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (999942347413/1000000000000:ℝ) ≤ taylorCos (3355583/312500000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (199996235509/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (61359231/10000000000:ℝ) + taylorErr ≤ (199996235509/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (1227176467/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (1227176467/200000000000:ℝ) ≤ taylorSin (61359231/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (199996235509/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (1227176467/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (5368830757/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6289321230331/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1258784634539/200000000000:ℝ) := by nlinarith
  have hp1 : (5204408857083/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1302054257747/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (3193364037/50000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (111848143141/1000000000000:ℝ) := by nlinarith
  have hN : (55505887767/62500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (3129077512303/40000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (55505887767/62500000000:ℝ) (3129077512303/40000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (10069211/78125000000:ℝ) ≤ ((55505887767/62500000000:ℝ)/(3129077512303/40000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_116 (x : ℝ) (h₁ : (1025/512:ℝ) ≤ x) (h₂ : x ≤ (2053/1024:ℝ)) : (143699471/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (61359231/10000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (153398079/10000000000:ℝ) := by nlinarith
  have hc1 : (124985293149/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (124985293149/125000000000:ℝ) ≤ taylorCos (153398079/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (199996235509/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (61359231/10000000000:ℝ) + taylorErr ≤ (199996235509/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (1227176467/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (1227176467/200000000000:ℝ) ≤ taylorSin (61359231/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (199996235509/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (1227176467/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1917401071/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6289321230331/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6298525115059/1000000000000:ℝ) := by nlinarith
  have hp1 : (5204408857083/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10424050270163/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (3193364037/50000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (79948340609/500000000000:ℝ) := by nlinarith
  have hN : (419992831987/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (39171418625029/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (419992831987/500000000000:ℝ) (39171418625029/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (143699471/1250000000000:ℝ) ≤ ((419992831987/500000000000:ℝ)/(39171418625029/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_117 (x : ℝ) (h₁ : (1025/512:ℝ) ≤ x) (h₂ : x ≤ (257/128:ℝ)) : (179073511/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (61359231/10000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (245436927/10000000000:ℝ) := by nlinarith
  have hc1 : (62481176027/62500000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (62481176027/62500000000:ℝ) ≤ taylorCos (245436927/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (199996235509/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (61359231/10000000000:ℝ) + taylorErr ≤ (199996235509/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (1227176467/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (1227176467/200000000000:ℝ) ≤ taylorSin (61359231/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (199996235509/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (1227176467/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (24541230879/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6289321230331/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3153864499893/500000000000:ℝ) := by nlinarith
  have hp1 : (5204408857083/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5219641343267/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (3193364037/50000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (128096423311/500000000000:ℝ) := by nlinarith
  have hN : (74350596981/100000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (78574890269483/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (74350596981/100000000000:ℝ) (78574890269483/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (179073511/2000000000000:ℝ) ≤ ((74350596981/100000000000:ℝ)/(78574890269483/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_118 (x : ℝ) (h₁ : (16403/8192:ℝ) ≤ x) (h₂ : x ≤ (8203/4096:ℝ)) : (1361538899/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (72864087/10000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (5273059/625000000:ℝ) := by nlinarith
  have hc1 : (199992881471/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (199992881471/200000000000:ℝ) ≤ taylorCos (5273059/625000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (124996682063/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (72864087/10000000000:ℝ) + taylorErr ≤ (124996682063/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (7286341963/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (7286341963/1000000000000:ℝ) ≤ taylorSin (72864087/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (8436796571/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (5273059/625000000:ℝ) + taylorErr ≤ (8436796571/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (199992881471/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (124996682063/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (7286341963/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (8436796571/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3145235857961/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6291622201513/1000000000000:ℝ) := by nlinarith
  have hp1 : (10410721766187/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10412625957883/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (7585607887/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (87849206977/1000000000000:ℝ) := by nlinarith
  have hN : (456057600189/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (78169019853143/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (456057600189/500000000000:ℝ) (78169019853143/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1361538899/10000000000000:ℝ) ≤ ((456057600189/500000000000:ℝ)/(78169019853143/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_119 (x : ℝ) (h₁ : (8203/4096:ℝ) ≤ x) (h₂ : x ≤ (16409/8192:ℝ)) : (132494461/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (84368943/10000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (479369/50000000:ℝ) := by nlinarith
  have hc1 : (499977019581/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (499977019581/500000000000:ℝ) ≤ taylorCos (479369/50000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (999964411881/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (84368943/10000000000:ℝ) + taylorErr ≤ (999964411881/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (8436791947/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (8436791947/1000000000000:ℝ) ≤ taylorSin (84368943/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (2396808847/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (479369/50000000:ℝ) + taylorErr ≤ (2396808847/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (499977019581/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999964411881/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (8436791947/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (2396808847/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (786452775189/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (24581143309/3906250000:ℝ) := by nlinarith
  have hp1 : (10412625818207/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1041453000993/100000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1756983153/20000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (99846550661/1000000000000:ℝ) := by nlinarith
  have hN : (900107488501/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (125116761893/1600000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (900107488501/1000000000000:ℝ) (125116761893/1600000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (132494461/1000000000000:ℝ) ≤ ((900107488501/1000000000000:ℝ)/(125116761893/1600000000:ℝ))^2 := by norm_num
  linarith

end Zeta23Ext.Bridge.ThreePoint
