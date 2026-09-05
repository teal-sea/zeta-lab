import FourPoint.Base

noncomputable section
open Real
namespace Zeta23Ext.Bridge.FourPoint


theorem wc_960 (x : ℝ) (h₁ : (8339/2048:ℝ) ≤ x) (h₂ : x ≤ (66727/16384:ℝ)) : (1326087369/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1127475879/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1141856949/5000000000:ℝ) := by nlinarith
  have hc1 : (974036387837/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (974036387837/1000000000000:ℝ) ≤ taylorCos (1141856949/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (194936702591/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1127475879/5000000000:ℝ) + taylorErr ≤ (194936702591/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (223589026949/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (223589026949/1000000000000:ℝ) ≤ taylorSin (1127475879/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (14149468821/62500000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1141856949/5000000000:ℝ) + taylorErr ≤ (14149468821/62500000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (974036387837/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (194936702591/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (223589026949/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (14149468821/62500000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6395932895089/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3198685501039/250000000000:ℝ) := by nlinarith
  have hp1 : (21170519736203/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21175280150301/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2366747953911/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (2396951730101/500000000000:ℝ) := by nlinarith
  have hN : (3758812394867/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (81602711476457/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3758812394867/1000000000000:ℝ) (81602711476457/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1326087369/10000000000000:ℝ) ≤ ((3758812394867/1000000000000:ℝ)/(81602711476457/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_961 (x : ℝ) (h₁ : (8339/2048:ℝ) ≤ x) (h₂ : x ≤ (16683/4096:ℝ)) : (33142219/250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1127475879/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1146650639/5000000000:ℝ) := by nlinarith
  have hc1 : (973818890081/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (973818890081/1000000000000:ℝ) ≤ taylorCos (1146650639/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (194936702591/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1127475879/5000000000:ℝ) + taylorErr ≤ (194936702591/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (223589026949/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (223589026949/1000000000000:ℝ) ≤ taylorSin (1127475879/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (113662621323/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1146650639/5000000000:ℝ) + taylorErr ≤ (113662621323/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (973818890081/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (194936702591/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (223589026949/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (113662621323/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6395932895089/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12795700742149/1000000000000:ℝ) := by nlinarith
  have hp1 : (21170519736203/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21176866860341/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2366747953911/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (481403639751/100000000000:ℝ) := by nlinarith
  have hN : (3758812394867/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (65291982993053/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3758812394867/1000000000000:ℝ) (65291982993053/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (33142219/250000000000:ℝ) ≤ ((3758812394867/1000000000000:ℝ)/(65291982993053/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_962 (x : ℝ) (h₁ : (8339/2048:ℝ) ≤ x) (h₂ : x ≤ (66737/16384:ℝ)) : (1325290301/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1127475879/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1151444329/5000000000:ℝ) := by nlinarith
  have hc1 : (973600497211/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (973600497211/1000000000000:ℝ) ≤ taylorCos (1151444329/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (194936702591/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1127475879/5000000000:ℝ) + taylorErr ≤ (194936702591/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (223589026949/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (223589026949/1000000000000:ℝ) ≤ taylorSin (1127475879/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (57064693801/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1151444329/5000000000:ℝ) + taylorErr ≤ (57064693801/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (973600497211/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (194936702591/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (223589026949/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (57064693801/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6395932895089/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12796659480141/1000000000000:ℝ) := by nlinarith
  have hp1 : (21170519736203/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21178453570379/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2366747953911/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (483416787269/100000000000:ℝ) := by nlinarith
  have hN : (3758812394867/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (163254493850683/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3758812394867/1000000000000:ℝ) (163254493850683/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1325290301/10000000000000:ℝ) ≤ ((3758812394867/1000000000000:ℝ)/(163254493850683/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_963 (x : ℝ) (h₁ : (8339/2048:ℝ) ≤ x) (h₂ : x ≤ (33371/8192:ℝ)) : (1324891991/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1127475879/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1156238019/5000000000:ℝ) := by nlinarith
  have hc1 : (973381209429/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (973381209429/1000000000000:ℝ) ≤ taylorCos (1156238019/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (194936702591/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1127475879/5000000000:ℝ) + taylorErr ≤ (194936702591/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (223589026949/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (223589026949/1000000000000:ℝ) ≤ taylorSin (1127475879/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (229192097951/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1156238019/5000000000:ℝ) + taylorErr ≤ (229192097951/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (973381209429/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (194936702591/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (223589026949/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (229192097951/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6395932895089/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12797618218133/1000000000000:ℝ) := by nlinarith
  have hp1 : (21170519736203/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21180040280417/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2366747953911/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1213574466639/250000000000:ℝ) := by nlinarith
  have hN : (3758812394867/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (16327903205709/50000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3758812394867/1000000000000:ℝ) (16327903205709/50000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1324891991/10000000000000:ℝ) ≤ ((3758812394867/1000000000000:ℝ)/(16327903205709/50000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_964 (x : ℝ) (h₁ : (8339/2048:ℝ) ≤ x) (h₂ : x ≤ (1043/256:ℝ)) : (1324095821/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1127475879/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1165825399/5000000000:ℝ) := by nlinarith
  have hc1 : (486469974967/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (486469974967/500000000000:ℝ) ≤ taylorCos (1165825399/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (194936702591/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1127475879/5000000000:ℝ) + taylorErr ≤ (194936702591/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (223589026949/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (223589026949/1000000000000:ℝ) ≤ taylorSin (1127475879/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (231058110583/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1165825399/5000000000:ℝ) + taylorErr ≤ (231058110583/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (486469974967/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (194936702591/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (223589026949/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (231058110583/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6395932895089/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6399767847059/500000000000:ℝ) := by nlinarith
  have hp1 : (21170519736203/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10591606850247/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2366747953911/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (4894553333713/1000000000000:ℝ) := by nlinarith
  have hN : (3758812394867/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (163328113985001/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3758812394867/1000000000000:ℝ) (163328113985001/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1324095821/10000000000000:ℝ) ≤ ((3758812394867/1000000000000:ℝ)/(163328113985001/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_965 (x : ℝ) (h₁ : (8339/2048:ℝ) ≤ x) (h₂ : x ≤ (33381/8192:ℝ)) : (1323300249/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1127475879/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1175412779/5000000000:ℝ) := by nlinarith
  have hc1 : (486247556609/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (486247556609/500000000000:ℝ) ≤ taylorCos (1175412779/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (194936702591/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1127475879/5000000000:ℝ) + taylorErr ≤ (194936702591/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (223589026949/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (223589026949/1000000000000:ℝ) ≤ taylorSin (1127475879/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (2911540921/12500000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1175412779/5000000000:ℝ) + taylorErr ≤ (2911540921/12500000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (486247556609/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (194936702591/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (223589026949/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (2911540921/12500000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6395932895089/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12801453170103/1000000000000:ℝ) := by nlinarith
  have hp1 : (21170519736203/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5296596780143/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2366747953911/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (616850330697/125000000000:ℝ) := by nlinarith
  have hN : (3758812394867/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (326754406532681/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3758812394867/1000000000000:ℝ) (326754406532681/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1323300249/10000000000000:ℝ) ≤ ((3758812394867/1000000000000:ℝ)/(326754406532681/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_966 (x : ℝ) (h₁ : (8339/2048:ℝ) ≤ x) (h₂ : x ≤ (16693/4096:ℝ)) : (52900211/400000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1127475879/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1185000159/5000000000:ℝ) := by nlinarith
  have hc1 : (243011675229/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (243011675229/250000000000:ℝ) ≤ taylorCos (1185000159/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (194936702591/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1127475879/5000000000:ℝ) + taylorErr ≤ (194936702591/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (223589026949/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (223589026949/1000000000000:ℝ) ≤ taylorSin (1127475879/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (117393790193/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1185000159/5000000000:ℝ) + taylorErr ≤ (117393790193/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (243011675229/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (194936702591/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (223589026949/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (117393790193/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6395932895089/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1600421330761/125000000000:ℝ) := by nlinarith
  have hp1 : (21170519736203/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21189560540649/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2366747953911/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (2487522824391/500000000000:ℝ) := by nlinarith
  have hN : (3758812394867/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (40856574975277/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3758812394867/1000000000000:ℝ) (40856574975277/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (52900211/400000000000:ℝ) ≤ ((3758812394867/1000000000000:ℝ)/(40856574975277/125000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_967 (x : ℝ) (h₁ : (8339/2048:ℝ) ≤ x) (h₂ : x ≤ (8349/2048:ℝ)) : (660458559/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1127475879/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2408349837/10000000000:ℝ) := by nlinarith
  have hc1 : (971139156187/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (971139156187/1000000000000:ℝ) ≤ taylorCos (2408349837/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (194936702591/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1127475879/5000000000:ℝ) + taylorErr ≤ (194936702591/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (223589026949/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (223589026949/1000000000000:ℝ) ≤ taylorSin (1127475879/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (59628399277/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2408349837/10000000000:ℝ) + taylorErr ≤ (59628399277/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (971139156187/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (194936702591/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (223589026949/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (59628399277/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6395932895089/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6403602799029/500000000000:ℝ) := by nlinarith
  have hp1 : (21170519736203/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (4239181476161/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2366747953911/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1263878028341/250000000000:ℝ) := by nlinarith
  have hN : (3758812394867/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (327049030461857/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3758812394867/1000000000000:ℝ) (327049030461857/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (660458559/5000000000000:ℝ) ≤ ((3758812394867/1000000000000:ℝ)/(327049030461857/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_968 (x : ℝ) (h₁ : (8339/2048:ℝ) ≤ x) (h₂ : x ≤ (16703/4096:ℝ)) : (659665673/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1127475879/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2446699357/10000000000:ℝ) := by nlinarith
  have hc1 : (121277166131/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (121277166131/125000000000:ℝ) ≤ taylorCos (2446699357/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (194936702591/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1127475879/5000000000:ℝ) + taylorErr ≤ (194936702591/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (223589026949/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (223589026949/1000000000000:ℝ) ≤ taylorSin (1127475879/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (242236106147/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2446699357/10000000000:ℝ) + taylorErr ≤ (242236106147/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (121277166131/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (194936702591/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (223589026949/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (242236106147/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6395932895089/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12811040550027/1000000000000:ℝ) := by nlinarith
  have hp1 : (21170519736203/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10601127110479/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2366747953911/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (641993938003/125000000000:ℝ) := by nlinarith
  have hN : (3758812394867/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (327245519948873/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3758812394867/1000000000000:ℝ) (327245519948873/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (659665673/5000000000000:ℝ) ≤ ((3758812394867/1000000000000:ℝ)/(327245519948873/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_969 (x : ℝ) (h₁ : (8339/2048:ℝ) ≤ x) (h₂ : x ≤ (4177/1024:ℝ)) : (263549591/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1127475879/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2485048877/10000000000:ℝ) := by nlinarith
  have hc1 : (969281233079/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (969281233079/1000000000000:ℝ) ≤ taylorCos (2485048877/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (194936702591/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1127475879/5000000000:ℝ) + taylorErr ≤ (194936702591/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (223589026949/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (223589026949/1000000000000:ℝ) ≤ taylorSin (1127475879/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (245955052659/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2485048877/10000000000:ℝ) + taylorErr ≤ (245955052659/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (969281233079/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (194936702591/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (223589026949/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (245955052659/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6395932895089/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12814875501997/1000000000000:ℝ) := by nlinarith
  have hp1 : (21170519736203/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21208601061113/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2366747953911/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (521636259081/100000000000:ℝ) := by nlinarith
  have hN : (3758812394867/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (163721034131683/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3758812394867/1000000000000:ℝ) (163721034131683/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (263549591/2000000000000:ℝ) ≤ ((3758812394867/1000000000000:ℝ)/(163721034131683/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_970 (x : ℝ) (h₁ : (8339/2048:ℝ) ≤ x) (h₂ : x ≤ (8359/2048:ℝ)) : (262917659/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1127475879/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (640436979/2500000000:ℝ) := by nlinarith
  have hc1 : (483683144977/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (483683144977/500000000000:ℝ) ≤ taylorCos (640436979/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (194936702591/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1127475879/5000000000:ℝ) + taylorErr ≤ (194936702591/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (223589026949/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (223589026949/1000000000000:ℝ) ≤ taylorSin (1127475879/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (3167275491/12500000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (640436979/2500000000:ℝ) + taylorErr ≤ (3167275491/12500000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (483683144977/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (194936702591/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (223589026949/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (3167275491/12500000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6395932895089/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12822545405937/1000000000000:ℝ) := by nlinarith
  have hp1 : (21170519736203/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1326330921339/62500000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2366747953911/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (336068433609/62500000000:ℝ) := by nlinarith
  have hN : (3758812394867/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (327835341374633/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3758812394867/1000000000000:ℝ) (327835341374633/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (262917659/2000000000000:ℝ) ≤ ((3758812394867/1000000000000:ℝ)/(327835341374633/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_971 (x : ℝ) (h₁ : (8339/2048:ℝ) ≤ x) (h₂ : x ≤ (2091/512:ℝ)) : (655719053/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1127475879/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (659611739/2500000000:ℝ) := by nlinarith
  have hc1 : (482697219707/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (482697219707/500000000000:ℝ) ≤ taylorCos (659611739/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (194936702591/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1127475879/5000000000:ℝ) + taylorErr ≤ (194936702591/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (223589026949/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (223589026949/1000000000000:ℝ) ≤ taylorSin (1127475879/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (130397060129/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (659611739/2500000000:ℝ) + taylorErr ≤ (130397060129/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (482697219707/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (194936702591/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (223589026949/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (130397060129/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6395932895089/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3207553827469/250000000000:ℝ) := by nlinarith
  have hp1 : (21170519736203/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21233988421733/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2366747953911/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1107539866003/200000000000:ℝ) := by nlinarith
  have hN : (3758812394867/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (164114424897777/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3758812394867/1000000000000:ℝ) (164114424897777/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (655719053/5000000000000:ℝ) ≤ ((3758812394867/1000000000000:ℝ)/(164114424897777/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_972 (x : ℝ) (h₁ : (66717/16384:ℝ) ≤ x) (h₂ : x ≤ (16683/4096:ℝ)) : (1340083459/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1132269569/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1146650639/5000000000:ℝ) := by nlinarith
  have hc1 : (973818890081/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (973818890081/1000000000000:ℝ) ≤ taylorCos (1146650639/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (194893740347/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1132269569/5000000000:ℝ) + taylorErr ≤ (194893740347/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (112261695083/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (112261695083/500000000000:ℝ) ≤ taylorSin (1132269569/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (113662621323/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1146650639/5000000000:ℝ) + taylorErr ≤ (113662621323/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (973818890081/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (194893740347/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (112261695083/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (113662621323/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1279282452817/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12795700742149/1000000000000:ℝ) := by nlinarith
  have hp1 : (1058605322311/50000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21176866860341/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (237681655813/50000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (481403639751/100000000000:ℝ) := by nlinarith
  have hN : (151166576581/40000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (65291982993053/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (151166576581/40000000000:ℝ) (65291982993053/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1340083459/10000000000000:ℝ) ≤ ((151166576581/40000000000:ℝ)/(65291982993053/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_973 (x : ℝ) (h₁ : (66717/16384:ℝ) ≤ x) (h₂ : x ≤ (66737/16384:ℝ)) : (1339680673/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1132269569/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1151444329/5000000000:ℝ) := by nlinarith
  have hc1 : (973600497211/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (973600497211/1000000000000:ℝ) ≤ taylorCos (1151444329/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (194893740347/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1132269569/5000000000:ℝ) + taylorErr ≤ (194893740347/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (112261695083/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (112261695083/500000000000:ℝ) ≤ taylorSin (1132269569/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (57064693801/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1151444329/5000000000:ℝ) + taylorErr ≤ (57064693801/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (973600497211/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (194893740347/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (112261695083/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (57064693801/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1279282452817/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12796659480141/1000000000000:ℝ) := by nlinarith
  have hp1 : (1058605322311/50000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21178453570379/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (237681655813/50000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (483416787269/100000000000:ℝ) := by nlinarith
  have hN : (151166576581/40000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (163254493850683/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (151166576581/40000000000:ℝ) (163254493850683/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1339680673/10000000000000:ℝ) ≤ ((151166576581/40000000000:ℝ)/(163254493850683/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_974 (x : ℝ) (h₁ : (66717/16384:ℝ) ≤ x) (h₂ : x ≤ (33371/8192:ℝ)) : (669639019/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1132269569/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1156238019/5000000000:ℝ) := by nlinarith
  have hc1 : (973381209429/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (973381209429/1000000000000:ℝ) ≤ taylorCos (1156238019/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (194893740347/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1132269569/5000000000:ℝ) + taylorErr ≤ (194893740347/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (112261695083/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (112261695083/500000000000:ℝ) ≤ taylorSin (1132269569/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (229192097951/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1156238019/5000000000:ℝ) + taylorErr ≤ (229192097951/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (973381209429/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (194893740347/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (112261695083/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (229192097951/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1279282452817/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12797618218133/1000000000000:ℝ) := by nlinarith
  have hp1 : (1058605322311/50000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21180040280417/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (237681655813/50000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1213574466639/250000000000:ℝ) := by nlinarith
  have hN : (151166576581/40000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (16327903205709/50000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (151166576581/40000000000:ℝ) (16327903205709/50000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (669639019/5000000000000:ℝ) ≤ ((151166576581/40000000000:ℝ)/(16327903205709/50000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_975 (x : ℝ) (h₁ : (33361/8192:ℝ) ≤ x) (h₂ : x ≤ (66737/16384:ℝ)) : (338537097/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1137063259/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1151444329/5000000000:ℝ) := by nlinarith
  have hc1 : (973600497211/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (973600497211/1000000000000:ℝ) ≤ taylorCos (1151444329/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (243563248701/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1137063259/5000000000:ℝ) + taylorErr ≤ (243563248701/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (225457547007/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (225457547007/1000000000000:ℝ) ≤ taylorSin (1137063259/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (57064693801/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1151444329/5000000000:ℝ) + taylorErr ≤ (57064693801/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (973600497211/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (243563248701/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (225457547007/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (57064693801/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12793783266163/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12796659480141/1000000000000:ℝ) := by nlinarith
  have hp1 : (10586846578119/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21178453570379/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1193442230021/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (483416787269/100000000000:ℝ) := by nlinarith
  have hN : (23746974533/6250000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (163254493850683/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (23746974533/6250000000:ℝ) (163254493850683/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (338537097/2500000000000:ℝ) ≤ ((23746974533/6250000000:ℝ)/(163254493850683/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_976 (x : ℝ) (h₁ : (33361/8192:ℝ) ≤ x) (h₂ : x ≤ (33371/8192:ℝ)) : (676870703/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1137063259/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1156238019/5000000000:ℝ) := by nlinarith
  have hc1 : (973381209429/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (973381209429/1000000000000:ℝ) ≤ taylorCos (1156238019/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (243563248701/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1137063259/5000000000:ℝ) + taylorErr ≤ (243563248701/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (225457547007/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (225457547007/1000000000000:ℝ) ≤ taylorSin (1137063259/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (229192097951/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1156238019/5000000000:ℝ) + taylorErr ≤ (229192097951/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (973381209429/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (243563248701/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (225457547007/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (229192097951/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12793783266163/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12797618218133/1000000000000:ℝ) := by nlinarith
  have hp1 : (10586846578119/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21180040280417/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1193442230021/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1213574466639/250000000000:ℝ) := by nlinarith
  have hN : (23746974533/6250000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (16327903205709/50000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (23746974533/6250000000:ℝ) (16327903205709/50000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (676870703/5000000000000:ℝ) ≤ ((23746974533/6250000000:ℝ)/(16327903205709/50000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_977 (x : ℝ) (h₁ : (33361/8192:ℝ) ≤ x) (h₂ : x ≤ (66747/16384:ℝ)) : (84583411/625000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1137063259/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1161031709/5000000000:ℝ) := by nlinarith
  have hc1 : (121645128367/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (121645128367/125000000000:ℝ) ≤ taylorCos (1161031709/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (243563248701/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1137063259/5000000000:ℝ) + taylorErr ≤ (243563248701/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (225457547007/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (225457547007/1000000000000:ℝ) ≤ taylorSin (1137063259/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (23012521003/100000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1161031709/5000000000:ℝ) + taylorErr ≤ (23012521003/100000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (121645128367/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (243563248701/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (225457547007/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (23012521003/100000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12793783266163/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6399288478063/500000000000:ℝ) := by nlinarith
  have hp1 : (10586846578119/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2647703373807/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1193442230021/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1218606589989/250000000000:ℝ) := by nlinarith
  have hN : (23746974533/6250000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (326607144203759/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (23746974533/6250000000:ℝ) (326607144203759/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (84583411/625000000000:ℝ) ≤ ((23746974533/6250000000:ℝ)/(326607144203759/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_978 (x : ℝ) (h₁ : (33361/8192:ℝ) ≤ x) (h₂ : x ≤ (1043/256:ℝ)) : (1352927899/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1137063259/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1165825399/5000000000:ℝ) := by nlinarith
  have hc1 : (486469974967/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (486469974967/500000000000:ℝ) ≤ taylorCos (1165825399/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (243563248701/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1137063259/5000000000:ℝ) + taylorErr ≤ (243563248701/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (225457547007/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (225457547007/1000000000000:ℝ) ≤ taylorSin (1137063259/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (231058110583/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1165825399/5000000000:ℝ) + taylorErr ≤ (231058110583/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (486469974967/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (243563248701/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (225457547007/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (231058110583/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12793783266163/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6399767847059/500000000000:ℝ) := by nlinarith
  have hp1 : (10586846578119/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10591606850247/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1193442230021/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (4894553333713/1000000000000:ℝ) := by nlinarith
  have hN : (23746974533/6250000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (163328113985001/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (23746974533/6250000000:ℝ) (163328113985001/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1352927899/10000000000000:ℝ) ≤ ((23746974533/6250000000:ℝ)/(163328113985001/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_979 (x : ℝ) (h₁ : (33361/8192:ℝ) ≤ x) (h₂ : x ≤ (33381/8192:ℝ)) : (338028751/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1137063259/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1175412779/5000000000:ℝ) := by nlinarith
  have hc1 : (486247556609/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (486247556609/500000000000:ℝ) ≤ taylorCos (1175412779/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (243563248701/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1137063259/5000000000:ℝ) + taylorErr ≤ (243563248701/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (225457547007/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (225457547007/1000000000000:ℝ) ≤ taylorSin (1137063259/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (2911540921/12500000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1175412779/5000000000:ℝ) + taylorErr ≤ (2911540921/12500000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (486247556609/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (243563248701/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (225457547007/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (2911540921/12500000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12793783266163/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12801453170103/1000000000000:ℝ) := by nlinarith
  have hp1 : (10586846578119/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5296596780143/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1193442230021/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (616850330697/125000000000:ℝ) := by nlinarith
  have hN : (23746974533/6250000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (326754406532681/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (23746974533/6250000000:ℝ) (326754406532681/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (338028751/2500000000000:ℝ) ≤ ((23746974533/6250000000:ℝ)/(326754406532681/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_980 (x : ℝ) (h₁ : (33361/8192:ℝ) ≤ x) (h₂ : x ≤ (16693/4096:ℝ)) : (1351302719/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1137063259/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1185000159/5000000000:ℝ) := by nlinarith
  have hc1 : (243011675229/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (243011675229/250000000000:ℝ) ≤ taylorCos (1185000159/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (243563248701/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1137063259/5000000000:ℝ) + taylorErr ≤ (243563248701/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (225457547007/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (225457547007/1000000000000:ℝ) ≤ taylorSin (1137063259/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (117393790193/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1185000159/5000000000:ℝ) + taylorErr ≤ (117393790193/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (243011675229/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (243563248701/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (225457547007/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (117393790193/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12793783266163/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1600421330761/125000000000:ℝ) := by nlinarith
  have hp1 : (10586846578119/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21189560540649/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1193442230021/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (2487522824391/500000000000:ℝ) := by nlinarith
  have hN : (23746974533/6250000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (40856574975277/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (23746974533/6250000000:ℝ) (40856574975277/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1351302719/10000000000000:ℝ) ≤ ((23746974533/6250000000:ℝ)/(40856574975277/125000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_981 (x : ℝ) (h₁ : (66727/16384:ℝ) ≤ x) (h₂ : x ≤ (33371/8192:ℝ)) : (171035259/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2283713897/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1156238019/5000000000:ℝ) := by nlinarith
  have hc1 : (973381209429/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (973381209429/1000000000000:ℝ) ≤ taylorCos (1156238019/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (15219318631/15625000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2283713897/10000000000:ℝ) + taylorErr ≤ (15219318631/15625000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (113195748257/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (113195748257/500000000000:ℝ) ≤ taylorSin (2283713897/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (229192097951/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1156238019/5000000000:ℝ) + taylorErr ≤ (229192097951/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (973381209429/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (15219318631/15625000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (113195748257/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (229192097951/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (2558948400831/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12797618218133/1000000000000:ℝ) := by nlinarith
  have hp1 : (4235055973251/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21180040280417/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (599237912253/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1213574466639/250000000000:ℝ) := by nlinarith
  have hN : (95496672641/25000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (16327903205709/50000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (95496672641/25000000000:ℝ) (16327903205709/50000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (171035259/1250000000000:ℝ) ≤ ((95496672641/25000000000:ℝ)/(16327903205709/50000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_982 (x : ℝ) (h₁ : (66727/16384:ℝ) ≤ x) (h₂ : x ≤ (66747/16384:ℝ)) : (170983859/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2283713897/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1161031709/5000000000:ℝ) := by nlinarith
  have hc1 : (121645128367/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (121645128367/125000000000:ℝ) ≤ taylorCos (1161031709/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (15219318631/15625000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2283713897/10000000000:ℝ) + taylorErr ≤ (15219318631/15625000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (113195748257/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (113195748257/500000000000:ℝ) ≤ taylorSin (2283713897/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (23012521003/100000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1161031709/5000000000:ℝ) + taylorErr ≤ (23012521003/100000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (121645128367/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (15219318631/15625000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (113195748257/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (23012521003/100000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (2558948400831/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6399288478063/500000000000:ℝ) := by nlinarith
  have hp1 : (4235055973251/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2647703373807/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (599237912253/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1218606589989/250000000000:ℝ) := by nlinarith
  have hN : (95496672641/25000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (326607144203759/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (95496672641/25000000000:ℝ) (326607144203759/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (170983859/1250000000000:ℝ) ≤ ((95496672641/25000000000:ℝ)/(326607144203759/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_983 (x : ℝ) (h₁ : (66727/16384:ℝ) ≤ x) (h₂ : x ≤ (1043/256:ℝ)) : (1367459827/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2283713897/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1165825399/5000000000:ℝ) := by nlinarith
  have hc1 : (486469974967/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (486469974967/500000000000:ℝ) ≤ taylorCos (1165825399/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (15219318631/15625000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2283713897/10000000000:ℝ) + taylorErr ≤ (15219318631/15625000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (113195748257/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (113195748257/500000000000:ℝ) ≤ taylorSin (2283713897/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (231058110583/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1165825399/5000000000:ℝ) + taylorErr ≤ (231058110583/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (486469974967/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (15219318631/15625000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (113195748257/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (231058110583/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (2558948400831/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6399767847059/500000000000:ℝ) := by nlinarith
  have hp1 : (4235055973251/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10591606850247/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (599237912253/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (4894553333713/1000000000000:ℝ) := by nlinarith
  have hN : (95496672641/25000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (163328113985001/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (95496672641/25000000000:ℝ) (163328113985001/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1367459827/10000000000000:ℝ) ≤ ((95496672641/25000000000:ℝ)/(163328113985001/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_984 (x : ℝ) (h₁ : (16683/4096:ℝ) ≤ x) (h₂ : x ≤ (66747/16384:ℝ)) : (1382484427/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2293301277/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1161031709/5000000000:ℝ) := by nlinarith
  have hc1 : (121645128367/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (121645128367/125000000000:ℝ) ≤ taylorCos (1161031709/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (243454723657/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2293301277/10000000000:ℝ) + taylorErr ≤ (243454723657/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (28415654753/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (28415654753/125000000000:ℝ) ≤ taylorSin (2293301277/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (23012521003/100000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1161031709/5000000000:ℝ) + taylorErr ≤ (23012521003/100000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (121645128367/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (243454723657/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (28415654753/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (23012521003/100000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3198925185537/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6399288478063/500000000000:ℝ) := by nlinarith
  have hp1 : (21176866576273/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2647703373807/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4814036235053/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1218606589989/250000000000:ℝ) := by nlinarith
  have hN : (153608693617/40000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (326607144203759/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (153608693617/40000000000:ℝ) (326607144203759/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1382484427/10000000000000:ℝ) ≤ ((153608693617/40000000000:ℝ)/(326607144203759/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_985 (x : ℝ) (h₁ : (16683/4096:ℝ) ≤ x) (h₂ : x ≤ (1043/256:ℝ)) : (1382068991/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2293301277/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1165825399/5000000000:ℝ) := by nlinarith
  have hc1 : (486469974967/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (486469974967/500000000000:ℝ) ≤ taylorCos (1165825399/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (243454723657/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2293301277/10000000000:ℝ) + taylorErr ≤ (243454723657/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (28415654753/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (28415654753/125000000000:ℝ) ≤ taylorSin (2293301277/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (231058110583/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1165825399/5000000000:ℝ) + taylorErr ≤ (231058110583/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (486469974967/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (243454723657/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (28415654753/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (231058110583/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3198925185537/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6399767847059/500000000000:ℝ) := by nlinarith
  have hp1 : (21176866576273/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10591606850247/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4814036235053/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (4894553333713/1000000000000:ℝ) := by nlinarith
  have hN : (153608693617/40000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (163328113985001/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (153608693617/40000000000:ℝ) (163328113985001/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1382068991/10000000000000:ℝ) ≤ ((153608693617/40000000000:ℝ)/(163328113985001/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_986 (x : ℝ) (h₁ : (16683/4096:ℝ) ≤ x) (h₂ : x ≤ (66757/16384:ℝ)) : (1381653711/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2293301277/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1170619089/5000000000:ℝ) := by nlinarith
  have hc1 : (486358989313/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (486358989313/500000000000:ℝ) ≤ taylorCos (1170619089/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (243454723657/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2293301277/10000000000:ℝ) + taylorErr ≤ (243454723657/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (28415654753/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (28415654753/125000000000:ℝ) ≤ taylorSin (2293301277/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (7249712461/31250000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1170619089/5000000000:ℝ) + taylorErr ≤ (7249712461/31250000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (486358989313/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (243454723657/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (28415654753/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (7249712461/31250000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3198925185537/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12800494432111/1000000000000:ℝ) := by nlinarith
  have hp1 : (21176866576273/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10592400205267/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4814036235053/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (2457339384321/500000000000:ℝ) := by nlinarith
  have hN : (153608693617/40000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (32670531541301/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (153608693617/40000000000:ℝ) (32670531541301/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1381653711/10000000000000:ℝ) ≤ ((153608693617/40000000000:ℝ)/(32670531541301/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_987 (x : ℝ) (h₁ : (16683/4096:ℝ) ≤ x) (h₂ : x ≤ (33381/8192:ℝ)) : (690619293/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2293301277/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1175412779/5000000000:ℝ) := by nlinarith
  have hc1 : (486247556609/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (486247556609/500000000000:ℝ) ≤ taylorCos (1175412779/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (243454723657/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2293301277/10000000000:ℝ) + taylorErr ≤ (243454723657/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (28415654753/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (28415654753/125000000000:ℝ) ≤ taylorSin (2293301277/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (2911540921/12500000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1175412779/5000000000:ℝ) + taylorErr ≤ (2911540921/12500000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (486247556609/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (243454723657/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (28415654753/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (2911540921/12500000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3198925185537/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12801453170103/1000000000000:ℝ) := by nlinarith
  have hp1 : (21176866576273/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5296596780143/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4814036235053/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (616850330697/125000000000:ℝ) := by nlinarith
  have hN : (153608693617/40000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (326754406532681/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (153608693617/40000000000:ℝ) (326754406532681/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (690619293/5000000000000:ℝ) ≤ ((153608693617/40000000000:ℝ)/(326754406532681/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_988 (x : ℝ) (h₁ : (16683/4096:ℝ) ≤ x) (h₂ : x ≤ (16693/4096:ℝ)) : (690204403/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2293301277/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1185000159/5000000000:ℝ) := by nlinarith
  have hc1 : (243011675229/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (243011675229/250000000000:ℝ) ≤ taylorCos (1185000159/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (243454723657/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2293301277/10000000000:ℝ) + taylorErr ≤ (243454723657/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (28415654753/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (28415654753/125000000000:ℝ) ≤ taylorSin (2293301277/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (117393790193/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1185000159/5000000000:ℝ) + taylorErr ≤ (117393790193/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (243011675229/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (243454723657/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (28415654753/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (117393790193/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3198925185537/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1600421330761/125000000000:ℝ) := by nlinarith
  have hp1 : (21176866576273/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21189560540649/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4814036235053/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (2487522824391/500000000000:ℝ) := by nlinarith
  have hN : (153608693617/40000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (40856574975277/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (153608693617/40000000000:ℝ) (40856574975277/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (690204403/5000000000000:ℝ) ≤ ((153608693617/40000000000:ℝ)/(40856574975277/125000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_989 (x : ℝ) (h₁ : (16683/4096:ℝ) ≤ x) (h₂ : x ≤ (33391/8192:ℝ)) : (1379579649/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2293301277/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1194587539/5000000000:ℝ) := by nlinarith
  have hc1 : (971594714677/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (971594714677/1000000000000:ℝ) ≤ taylorCos (1194587539/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (243454723657/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2293301277/10000000000:ℝ) + taylorErr ≤ (243454723657/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (28415654753/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (28415654753/125000000000:ℝ) ≤ taylorSin (2293301277/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (47330204769/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1194587539/5000000000:ℝ) + taylorErr ≤ (47330204769/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (971594714677/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (243454723657/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (28415654753/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (47330204769/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3198925185537/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12805288122073/1000000000000:ℝ) := by nlinarith
  have hp1 : (21176866576273/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21192733960727/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4814036235053/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (5015282189881/1000000000000:ℝ) := by nlinarith
  have hN : (153608693617/40000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20434425486163/62500000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (153608693617/40000000000:ℝ) (20434425486163/62500000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1379579649/10000000000000:ℝ) ≤ ((153608693617/40000000000:ℝ)/(20434425486163/62500000000:ℝ))^2 := by norm_num
  linarith

theorem wc_990 (x : ℝ) (h₁ : (16683/4096:ℝ) ≤ x) (h₂ : x ≤ (8349/2048:ℝ)) : (275750223/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2293301277/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2408349837/10000000000:ℝ) := by nlinarith
  have hc1 : (971139156187/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (971139156187/1000000000000:ℝ) ≤ taylorCos (2408349837/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (243454723657/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2293301277/10000000000:ℝ) + taylorErr ≤ (243454723657/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (28415654753/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (28415654753/125000000000:ℝ) ≤ taylorSin (2293301277/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (59628399277/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2408349837/10000000000:ℝ) + taylorErr ≤ (59628399277/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (971139156187/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (243454723657/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (28415654753/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (59628399277/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3198925185537/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6403602799029/500000000000:ℝ) := by nlinarith
  have hp1 : (21176866576273/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (4239181476161/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4814036235053/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1263878028341/250000000000:ℝ) := by nlinarith
  have hN : (153608693617/40000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (327049030461857/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (153608693617/40000000000:ℝ) (327049030461857/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (275750223/2000000000000:ℝ) ≤ ((153608693617/40000000000:ℝ)/(327049030461857/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_991 (x : ℝ) (h₁ : (16683/4096:ℝ) ≤ x) (h₂ : x ≤ (16703/4096:ℝ)) : (172136989/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2293301277/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2446699357/10000000000:ℝ) := by nlinarith
  have hc1 : (121277166131/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (121277166131/125000000000:ℝ) ≤ taylorCos (2446699357/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (243454723657/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2293301277/10000000000:ℝ) + taylorErr ≤ (243454723657/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (28415654753/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (28415654753/125000000000:ℝ) ≤ taylorSin (2293301277/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (242236106147/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2446699357/10000000000:ℝ) + taylorErr ≤ (242236106147/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (121277166131/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (243454723657/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (28415654753/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (242236106147/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3198925185537/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12811040550027/1000000000000:ℝ) := by nlinarith
  have hp1 : (21176866576273/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10601127110479/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4814036235053/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (641993938003/125000000000:ℝ) := by nlinarith
  have hN : (153608693617/40000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (327245519948873/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (153608693617/40000000000:ℝ) (327245519948873/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (172136989/1250000000000:ℝ) ≤ ((153608693617/40000000000:ℝ)/(327245519948873/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_992 (x : ℝ) (h₁ : (16683/4096:ℝ) ≤ x) (h₂ : x ≤ (4177/1024:ℝ)) : (275088639/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2293301277/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2485048877/10000000000:ℝ) := by nlinarith
  have hc1 : (969281233079/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (969281233079/1000000000000:ℝ) ≤ taylorCos (2485048877/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (243454723657/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2293301277/10000000000:ℝ) + taylorErr ≤ (243454723657/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (28415654753/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (28415654753/125000000000:ℝ) ≤ taylorSin (2293301277/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (245955052659/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2485048877/10000000000:ℝ) + taylorErr ≤ (245955052659/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (969281233079/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (243454723657/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (28415654753/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (245955052659/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3198925185537/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12814875501997/1000000000000:ℝ) := by nlinarith
  have hp1 : (21176866576273/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21208601061113/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4814036235053/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (521636259081/100000000000:ℝ) := by nlinarith
  have hN : (153608693617/40000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (163721034131683/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (153608693617/40000000000:ℝ) (163721034131683/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (275088639/2000000000000:ℝ) ≤ ((153608693617/40000000000:ℝ)/(163721034131683/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_993 (x : ℝ) (h₁ : (66737/16384:ℝ) ≤ x) (h₂ : x ≤ (1043/256:ℝ)) : (174594421/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2302888657/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1165825399/5000000000:ℝ) := by nlinarith
  have hc1 : (486469974967/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (486469974967/500000000000:ℝ) ≤ taylorCos (1165825399/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (973600501759/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2302888657/10000000000:ℝ) + taylorErr ≤ (973600501759/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (114129385291/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (114129385291/500000000000:ℝ) ≤ taylorSin (2302888657/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (231058110583/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1165825399/5000000000:ℝ) + taylorErr ≤ (231058110583/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (486469974967/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (973600501759/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (114129385291/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (231058110583/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (639832974007/50000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6399767847059/500000000000:ℝ) := by nlinarith
  have hp1 : (2117845328629/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10591606850247/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1208541927489/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (4894553333713/1000000000000:ℝ) := by nlinarith
  have hN : (3860567208197/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (163328113985001/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3860567208197/1000000000000:ℝ) (163328113985001/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (174594421/1250000000000:ℝ) ≤ ((3860567208197/1000000000000:ℝ)/(163328113985001/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_994 (x : ℝ) (h₁ : (66737/16384:ℝ) ≤ x) (h₂ : x ≤ (66757/16384:ℝ)) : (55853427/400000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2302888657/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1170619089/5000000000:ℝ) := by nlinarith
  have hc1 : (486358989313/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (486358989313/500000000000:ℝ) ≤ taylorCos (1170619089/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (973600501759/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2302888657/10000000000:ℝ) + taylorErr ≤ (973600501759/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (114129385291/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (114129385291/500000000000:ℝ) ≤ taylorSin (2302888657/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (7249712461/31250000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1170619089/5000000000:ℝ) + taylorErr ≤ (7249712461/31250000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (486358989313/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (973600501759/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (114129385291/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (7249712461/31250000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (639832974007/50000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12800494432111/1000000000000:ℝ) := by nlinarith
  have hp1 : (2117845328629/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10592400205267/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1208541927489/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (2457339384321/500000000000:ℝ) := by nlinarith
  have hN : (3860567208197/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (32670531541301/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3860567208197/1000000000000:ℝ) (32670531541301/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (55853427/400000000000:ℝ) ≤ ((3860567208197/1000000000000:ℝ)/(32670531541301/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_995 (x : ℝ) (h₁ : (66737/16384:ℝ) ≤ x) (h₂ : x ≤ (33381/8192:ℝ)) : (1395916139/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2302888657/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1175412779/5000000000:ℝ) := by nlinarith
  have hc1 : (486247556609/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (486247556609/500000000000:ℝ) ≤ taylorCos (1175412779/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (973600501759/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2302888657/10000000000:ℝ) + taylorErr ≤ (973600501759/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (114129385291/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (114129385291/500000000000:ℝ) ≤ taylorSin (2302888657/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (2911540921/12500000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1175412779/5000000000:ℝ) + taylorErr ≤ (2911540921/12500000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (486247556609/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (973600501759/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (114129385291/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (2911540921/12500000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (639832974007/50000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12801453170103/1000000000000:ℝ) := by nlinarith
  have hp1 : (2117845328629/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5296596780143/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1208541927489/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (616850330697/125000000000:ℝ) := by nlinarith
  have hN : (3860567208197/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (326754406532681/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3860567208197/1000000000000:ℝ) (326754406532681/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1395916139/10000000000000:ℝ) ≤ ((3860567208197/1000000000000:ℝ)/(326754406532681/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_996 (x : ℝ) (h₁ : (33371/8192:ℝ) ≤ x) (h₂ : x ≤ (66757/16384:ℝ)) : (1411094809/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2312476037/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1170619089/5000000000:ℝ) := by nlinarith
  have hc1 : (486358989313/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (486358989313/500000000000:ℝ) ≤ taylorCos (1170619089/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (121672651747/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2312476037/10000000000:ℝ) + taylorErr ≤ (121672651747/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (22919209333/100000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (22919209333/100000000000:ℝ) ≤ taylorSin (2312476037/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (7249712461/31250000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1170619089/5000000000:ℝ) + taylorErr ≤ (7249712461/31250000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (486358989313/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (121672651747/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (22919209333/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (7249712461/31250000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3199404554533/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12800494432111/1000000000000:ℝ) := by nlinarith
  have hp1 : (21180039996307/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10592400205267/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2427148851783/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (2457339384321/500000000000:ℝ) := by nlinarith
  have hN : (388091648959/100000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (32670531541301/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (388091648959/100000000000:ℝ) (32670531541301/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1411094809/10000000000000:ℝ) ≤ ((388091648959/100000000000:ℝ)/(32670531541301/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_997 (x : ℝ) (h₁ : (33371/8192:ℝ) ≤ x) (h₂ : x ≤ (33381/8192:ℝ)) : (1410670839/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2312476037/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1175412779/5000000000:ℝ) := by nlinarith
  have hc1 : (486247556609/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (486247556609/500000000000:ℝ) ≤ taylorCos (1175412779/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (121672651747/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2312476037/10000000000:ℝ) + taylorErr ≤ (121672651747/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (22919209333/100000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (22919209333/100000000000:ℝ) ≤ taylorSin (2312476037/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (2911540921/12500000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1175412779/5000000000:ℝ) + taylorErr ≤ (2911540921/12500000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (486247556609/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (121672651747/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (22919209333/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (2911540921/12500000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3199404554533/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12801453170103/1000000000000:ℝ) := by nlinarith
  have hp1 : (21180039996307/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5296596780143/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2427148851783/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (616850330697/125000000000:ℝ) := by nlinarith
  have hN : (388091648959/100000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (326754406532681/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (388091648959/100000000000:ℝ) (326754406532681/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1410670839/10000000000000:ℝ) ≤ ((388091648959/100000000000:ℝ)/(326754406532681/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_998 (x : ℝ) (h₁ : (33371/8192:ℝ) ≤ x) (h₂ : x ≤ (66767/16384:ℝ)) : (1410247029/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2312476037/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1180206469/5000000000:ℝ) := by nlinarith
  have hc1 : (121533919239/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (121533919239/125000000000:ℝ) ≤ taylorCos (1180206469/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (121672651747/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2312476037/10000000000:ℝ) + taylorErr ≤ (121672651747/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (22919209333/100000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (22919209333/100000000000:ℝ) ≤ taylorSin (2312476037/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (233855534511/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1180206469/5000000000:ℝ) + taylorErr ≤ (233855534511/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (121533919239/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (121672651747/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (22919209333/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (233855534511/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3199404554533/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12502355379/976562500:ℝ) := by nlinarith
  have hp1 : (21180039996307/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21187973830611/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2427148851783/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (4954924945363/1000000000000:ℝ) := by nlinarith
  have hN : (388091648959/100000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (326803501329117/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (388091648959/100000000000:ℝ) (326803501329117/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1410247029/10000000000000:ℝ) ≤ ((388091648959/100000000000:ℝ)/(326803501329117/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_999 (x : ℝ) (h₁ : (33371/8192:ℝ) ≤ x) (h₂ : x ≤ (16693/4096:ℝ)) : (1409823377/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2312476037/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1185000159/5000000000:ℝ) := by nlinarith
  have hc1 : (243011675229/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (243011675229/250000000000:ℝ) ≤ taylorCos (1185000159/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (121672651747/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2312476037/10000000000:ℝ) + taylorErr ≤ (121672651747/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (22919209333/100000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (22919209333/100000000000:ℝ) ≤ taylorSin (2312476037/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (117393790193/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1185000159/5000000000:ℝ) + taylorErr ≤ (117393790193/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (243011675229/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (121672651747/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (22919209333/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (117393790193/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3199404554533/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1600421330761/125000000000:ℝ) := by nlinarith
  have hp1 : (21180039996307/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21189560540649/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2427148851783/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (2487522824391/500000000000:ℝ) := by nlinarith
  have hN : (388091648959/100000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (40856574975277/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (388091648959/100000000000:ℝ) (40856574975277/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1409823377/10000000000000:ℝ) ≤ ((388091648959/100000000000:ℝ)/(40856574975277/125000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1000 (x : ℝ) (h₁ : (33371/8192:ℝ) ≤ x) (h₂ : x ≤ (33391/8192:ℝ)) : (176122069/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2312476037/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1194587539/5000000000:ℝ) := by nlinarith
  have hc1 : (971594714677/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (971594714677/1000000000000:ℝ) ≤ taylorCos (1194587539/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (121672651747/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2312476037/10000000000:ℝ) + taylorErr ≤ (121672651747/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (22919209333/100000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (22919209333/100000000000:ℝ) ≤ taylorSin (2312476037/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (47330204769/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1194587539/5000000000:ℝ) + taylorErr ≤ (47330204769/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (971594714677/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (121672651747/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (22919209333/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (47330204769/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3199404554533/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12805288122073/1000000000000:ℝ) := by nlinarith
  have hp1 : (21180039996307/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21192733960727/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2427148851783/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (5015282189881/1000000000000:ℝ) := by nlinarith
  have hN : (388091648959/100000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20434425486163/62500000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (388091648959/100000000000:ℝ) (20434425486163/62500000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (176122069/1250000000000:ℝ) ≤ ((388091648959/100000000000:ℝ)/(20434425486163/62500000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1001 (x : ℝ) (h₁ : (33371/8192:ℝ) ≤ x) (h₂ : x ≤ (8349/2048:ℝ)) : (1408130363/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2312476037/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2408349837/10000000000:ℝ) := by nlinarith
  have hc1 : (971139156187/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (971139156187/1000000000000:ℝ) ≤ taylorCos (2408349837/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (121672651747/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2312476037/10000000000:ℝ) + taylorErr ≤ (121672651747/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (22919209333/100000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (22919209333/100000000000:ℝ) ≤ taylorSin (2312476037/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (59628399277/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2408349837/10000000000:ℝ) + taylorErr ≤ (59628399277/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (971139156187/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (121672651747/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (22919209333/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (59628399277/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3199404554533/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6403602799029/500000000000:ℝ) := by nlinarith
  have hp1 : (21180039996307/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (4239181476161/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2427148851783/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1263878028341/250000000000:ℝ) := by nlinarith
  have hN : (388091648959/100000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (327049030461857/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (388091648959/100000000000:ℝ) (327049030461857/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1408130363/10000000000000:ℝ) ≤ ((388091648959/100000000000:ℝ)/(327049030461857/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1002 (x : ℝ) (h₁ : (66747/16384:ℝ) ≤ x) (h₂ : x ≤ (33381/8192:ℝ)) : (285100533/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2322063417/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1175412779/5000000000:ℝ) := by nlinarith
  have hc1 : (486247556609/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (486247556609/500000000000:ℝ) ≤ taylorCos (1175412779/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (973161031483/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2322063417/10000000000:ℝ) + taylorErr ≤ (973161031483/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (230125205409/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (230125205409/1000000000000:ℝ) ≤ taylorSin (2322063417/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (2911540921/12500000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1175412779/5000000000:ℝ) + taylorErr ≤ (2911540921/12500000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (486247556609/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (973161031483/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (230125205409/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (2911540921/12500000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (102388615649/8000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12801453170103/1000000000000:ℝ) := by nlinarith
  have hp1 : (847265068253/40000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5296596780143/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4874426196689/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (616850330697/125000000000:ℝ) := by nlinarith
  have hN : (1950632582603/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (326754406532681/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1950632582603/500000000000:ℝ) (326754406532681/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (285100533/2000000000000:ℝ) ≤ ((1950632582603/500000000000:ℝ)/(326754406532681/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1003 (x : ℝ) (h₁ : (66747/16384:ℝ) ≤ x) (h₂ : x ≤ (66767/16384:ℝ)) : (712537199/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2322063417/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1180206469/5000000000:ℝ) := by nlinarith
  have hc1 : (121533919239/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (121533919239/125000000000:ℝ) ≤ taylorCos (1180206469/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (973161031483/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2322063417/10000000000:ℝ) + taylorErr ≤ (973161031483/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (230125205409/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (230125205409/1000000000000:ℝ) ≤ taylorSin (2322063417/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (233855534511/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1180206469/5000000000:ℝ) + taylorErr ≤ (233855534511/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (121533919239/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (973161031483/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (230125205409/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (233855534511/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (102388615649/8000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12502355379/976562500:ℝ) := by nlinarith
  have hp1 : (847265068253/40000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21187973830611/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4874426196689/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (4954924945363/1000000000000:ℝ) := by nlinarith
  have hN : (1950632582603/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (326803501329117/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1950632582603/500000000000:ℝ) (326803501329117/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (712537199/5000000000000:ℝ) ≤ ((1950632582603/500000000000:ℝ)/(326803501329117/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1004 (x : ℝ) (h₁ : (66747/16384:ℝ) ≤ x) (h₂ : x ≤ (16693/4096:ℝ)) : (356161573/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2322063417/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1185000159/5000000000:ℝ) := by nlinarith
  have hc1 : (243011675229/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (243011675229/250000000000:ℝ) ≤ taylorCos (1185000159/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (973161031483/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2322063417/10000000000:ℝ) + taylorErr ≤ (973161031483/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (230125205409/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (230125205409/1000000000000:ℝ) ≤ taylorSin (2322063417/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (117393790193/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1185000159/5000000000:ℝ) + taylorErr ≤ (117393790193/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (243011675229/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (973161031483/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (230125205409/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (117393790193/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (102388615649/8000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1600421330761/125000000000:ℝ) := by nlinarith
  have hp1 : (847265068253/40000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21189560540649/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4874426196689/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (2487522824391/500000000000:ℝ) := by nlinarith
  have hN : (1950632582603/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (40856574975277/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1950632582603/500000000000:ℝ) (40856574975277/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (356161573/2500000000000:ℝ) ≤ ((1950632582603/500000000000:ℝ)/(40856574975277/125000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1005 (x : ℝ) (h₁ : (1043/256:ℝ) ≤ x) (h₂ : x ≤ (66767/16384:ℝ)) : (1439978849/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2331650797/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1180206469/5000000000:ℝ) := by nlinarith
  have hc1 : (121533919239/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (121533919239/125000000000:ℝ) ≤ taylorCos (1180206469/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (972939954481/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2331650797/10000000000:ℝ) + taylorErr ≤ (972939954481/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (231058105961/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (231058105961/1000000000000:ℝ) ≤ taylorSin (2331650797/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (233855534511/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1180206469/5000000000:ℝ) + taylorErr ≤ (233855534511/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (121533919239/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (972939954481/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (231058105961/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (233855534511/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12799535694117/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12502355379/976562500:ℝ) := by nlinarith
  have hp1 : (10591606708171/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21187973830611/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4894553170147/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (4954924945363/1000000000000:ℝ) := by nlinarith
  have hN : (1960806607833/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (326803501329117/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1960806607833/500000000000:ℝ) (326803501329117/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1439978849/10000000000000:ℝ) ≤ ((1960806607833/500000000000:ℝ)/(326803501329117/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1006 (x : ℝ) (h₁ : (1043/256:ℝ) ≤ x) (h₂ : x ≤ (16693/4096:ℝ)) : (719773133/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2331650797/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1185000159/5000000000:ℝ) := by nlinarith
  have hc1 : (243011675229/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (243011675229/250000000000:ℝ) ≤ taylorCos (1185000159/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (972939954481/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2331650797/10000000000:ℝ) + taylorErr ≤ (972939954481/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (231058105961/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (231058105961/1000000000000:ℝ) ≤ taylorSin (2331650797/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (117393790193/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1185000159/5000000000:ℝ) + taylorErr ≤ (117393790193/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (243011675229/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (972939954481/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (231058105961/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (117393790193/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12799535694117/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1600421330761/125000000000:ℝ) := by nlinarith
  have hp1 : (10591606708171/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21189560540649/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4894553170147/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (2487522824391/500000000000:ℝ) := by nlinarith
  have hN : (1960806607833/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (40856574975277/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1960806607833/500000000000:ℝ) (40856574975277/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (719773133/5000000000000:ℝ) ≤ ((1960806607833/500000000000:ℝ)/(40856574975277/125000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1007 (x : ℝ) (h₁ : (1043/256:ℝ) ≤ x) (h₂ : x ≤ (66777/16384:ℝ)) : (287822769/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2331650797/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1189793849/5000000000:ℝ) := by nlinarith
  have hc1 : (194364230887/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (194364230887/200000000000:ℝ) ≤ taylorCos (1189793849/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (972939954481/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2331650797/10000000000:ℝ) + taylorErr ≤ (972939954481/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (231058105961/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (231058105961/1000000000000:ℝ) ≤ taylorSin (2331650797/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (235719410449/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1189793849/5000000000:ℝ) + taylorErr ≤ (235719410449/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (194364230887/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (972939954481/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (231058105961/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (235719410449/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12799535694117/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (160054117301/12500000000:ℝ) := by nlinarith
  have hp1 : (10591606708171/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21191147250687/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4894553170147/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (499516473667/100000000000:ℝ) := by nlinarith
  have hN : (1960806607833/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (32690170195203/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1960806607833/500000000000:ℝ) (32690170195203/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (287822769/2000000000000:ℝ) ≤ ((1960806607833/500000000000:ℝ)/(32690170195203/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1008 (x : ℝ) (h₁ : (1043/256:ℝ) ≤ x) (h₂ : x ≤ (33391/8192:ℝ)) : (1438681587/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2331650797/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1194587539/5000000000:ℝ) := by nlinarith
  have hc1 : (971594714677/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (971594714677/1000000000000:ℝ) ≤ taylorCos (1194587539/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (972939954481/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2331650797/10000000000:ℝ) + taylorErr ≤ (972939954481/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (231058105961/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (231058105961/1000000000000:ℝ) ≤ taylorSin (2331650797/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (47330204769/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1194587539/5000000000:ℝ) + taylorErr ≤ (47330204769/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (971594714677/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (972939954481/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (231058105961/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (47330204769/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12799535694117/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12805288122073/1000000000000:ℝ) := by nlinarith
  have hp1 : (10591606708171/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21192733960727/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4894553170147/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (5015282189881/1000000000000:ℝ) := by nlinarith
  have hN : (1960806607833/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20434425486163/62500000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1960806607833/500000000000:ℝ) (20434425486163/62500000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1438681587/10000000000000:ℝ) ≤ ((1960806607833/500000000000:ℝ)/(20434425486163/62500000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1009 (x : ℝ) (h₁ : (1043/256:ℝ) ≤ x) (h₂ : x ≤ (8349/2048:ℝ)) : (718908779/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2331650797/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2408349837/10000000000:ℝ) := by nlinarith
  have hc1 : (971139156187/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (971139156187/1000000000000:ℝ) ≤ taylorCos (2408349837/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (972939954481/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2331650797/10000000000:ℝ) + taylorErr ≤ (972939954481/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (231058105961/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (231058105961/1000000000000:ℝ) ≤ taylorSin (2331650797/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (59628399277/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2408349837/10000000000:ℝ) + taylorErr ≤ (59628399277/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (971139156187/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (972939954481/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (231058105961/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (59628399277/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12799535694117/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6403602799029/500000000000:ℝ) := by nlinarith
  have hp1 : (10591606708171/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (4239181476161/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4894553170147/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1263878028341/250000000000:ℝ) := by nlinarith
  have hN : (1960806607833/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (327049030461857/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1960806607833/500000000000:ℝ) (327049030461857/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (718908779/5000000000000:ℝ) ≤ ((1960806607833/500000000000:ℝ)/(327049030461857/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1010 (x : ℝ) (h₁ : (1043/256:ℝ) ≤ x) (h₂ : x ≤ (33401/8192:ℝ)) : (718477089/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2331650797/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2427524597/10000000000:ℝ) := by nlinarith
  have hc1 : (485340013537/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (485340013537/500000000000:ℝ) ≤ taylorCos (2427524597/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (972939954481/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2331650797/10000000000:ℝ) + taylorErr ≤ (972939954481/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (231058105961/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (231058105961/1000000000000:ℝ) ≤ taylorSin (2331650797/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (240375293523/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2427524597/10000000000:ℝ) + taylorErr ≤ (240375293523/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (485340013537/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (972939954481/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (231058105961/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (240375293523/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12799535694117/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12809123074043/1000000000000:ℝ) := by nlinarith
  have hp1 : (10591606708171/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10599540400441/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4894553170147/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (509573526993/100000000000:ℝ) := by nlinarith
  have hN : (1960806607833/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (163573633925981/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1960806607833/500000000000:ℝ) (163573633925981/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (718477089/5000000000000:ℝ) ≤ ((1960806607833/500000000000:ℝ)/(163573633925981/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1011 (x : ℝ) (h₁ : (1043/256:ℝ) ≤ x) (h₂ : x ≤ (16703/4096:ℝ)) : (718045723/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2331650797/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2446699357/10000000000:ℝ) := by nlinarith
  have hc1 : (121277166131/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (121277166131/125000000000:ℝ) ≤ taylorCos (2446699357/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (972939954481/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2331650797/10000000000:ℝ) + taylorErr ≤ (972939954481/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (231058105961/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (231058105961/1000000000000:ℝ) ≤ taylorSin (2331650797/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (242236106147/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2446699357/10000000000:ℝ) + taylorErr ≤ (242236106147/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (121277166131/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (972939954481/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (231058105961/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (242236106147/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12799535694117/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12811040550027/1000000000000:ℝ) := by nlinarith
  have hp1 : (10591606708171/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10601127110479/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4894553170147/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (641993938003/125000000000:ℝ) := by nlinarith
  have hN : (1960806607833/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (327245519948873/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1960806607833/500000000000:ℝ) (327245519948873/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (718045723/5000000000000:ℝ) ≤ ((1960806607833/500000000000:ℝ)/(327245519948873/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1012 (x : ℝ) (h₁ : (1043/256:ℝ) ≤ x) (h₂ : x ≤ (4177/1024:ℝ)) : (57374717/400000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2331650797/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2485048877/10000000000:ℝ) := by nlinarith
  have hc1 : (969281233079/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (969281233079/1000000000000:ℝ) ≤ taylorCos (2485048877/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (972939954481/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2331650797/10000000000:ℝ) + taylorErr ≤ (972939954481/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (231058105961/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (231058105961/1000000000000:ℝ) ≤ taylorSin (2331650797/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (245955052659/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2485048877/10000000000:ℝ) + taylorErr ≤ (245955052659/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (969281233079/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (972939954481/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (231058105961/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (245955052659/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12799535694117/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12814875501997/1000000000000:ℝ) := by nlinarith
  have hp1 : (10591606708171/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21208601061113/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4894553170147/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (521636259081/100000000000:ℝ) := by nlinarith
  have hN : (1960806607833/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (163721034131683/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1960806607833/500000000000:ℝ) (163721034131683/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (57374717/400000000000:ℝ) ≤ ((1960806607833/500000000000:ℝ)/(163721034131683/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1013 (x : ℝ) (h₁ : (1043/256:ℝ) ≤ x) (h₂ : x ≤ (16713/4096:ℝ)) : (1432646991/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2331650797/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2523398397/10000000000:ℝ) := by nlinarith
  have hc1 : (968330882047/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (968330882047/1000000000000:ℝ) ≤ taylorCos (2523398397/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (972939954481/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2331650797/10000000000:ℝ) + taylorErr ≤ (972939954481/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (231058105961/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (231058105961/1000000000000:ℝ) ≤ taylorSin (2331650797/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (249670381949/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2523398397/10000000000:ℝ) + taylorErr ≤ (249670381949/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (968330882047/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (972939954481/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (231058105961/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (249670381949/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12799535694117/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12818710453967/1000000000000:ℝ) := by nlinarith
  have hp1 : (10591606708171/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21214947901269/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4894553170147/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (2648372072769/500000000000:ℝ) := by nlinarith
  have hN : (1960806607833/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (163819337702643/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1960806607833/500000000000:ℝ) (163819337702643/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1432646991/10000000000000:ℝ) ≤ ((1960806607833/500000000000:ℝ)/(163819337702643/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1014 (x : ℝ) (h₁ : (1043/256:ℝ) ≤ x) (h₂ : x ≤ (8359/2048:ℝ)) : (715464319/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2331650797/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (640436979/2500000000:ℝ) := by nlinarith
  have hc1 : (483683144977/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (483683144977/500000000000:ℝ) ≤ taylorCos (640436979/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (972939954481/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2331650797/10000000000:ℝ) + taylorErr ≤ (972939954481/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (231058105961/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (231058105961/1000000000000:ℝ) ≤ taylorSin (2331650797/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (3167275491/12500000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (640436979/2500000000:ℝ) + taylorErr ≤ (3167275491/12500000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (483683144977/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (972939954481/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (231058105961/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (3167275491/12500000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12799535694117/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12822545405937/1000000000000:ℝ) := by nlinarith
  have hp1 : (10591606708171/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1326330921339/62500000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4894553170147/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (336068433609/62500000000:ℝ) := by nlinarith
  have hN : (1960806607833/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (327835341374633/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1960806607833/500000000000:ℝ) (327835341374633/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (715464319/5000000000000:ℝ) ≤ ((1960806607833/500000000000:ℝ)/(327835341374633/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1015 (x : ℝ) (h₁ : (1043/256:ℝ) ≤ x) (h₂ : x ≤ (2091/512:ℝ)) : (1427499659/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2331650797/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (659611739/2500000000:ℝ) := by nlinarith
  have hc1 : (482697219707/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (482697219707/500000000000:ℝ) ≤ taylorCos (659611739/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (972939954481/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2331650797/10000000000:ℝ) + taylorErr ≤ (972939954481/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (231058105961/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (231058105961/1000000000000:ℝ) ≤ taylorSin (2331650797/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (130397060129/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (659611739/2500000000:ℝ) + taylorErr ≤ (130397060129/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (482697219707/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (972939954481/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (231058105961/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (130397060129/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12799535694117/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3207553827469/250000000000:ℝ) := by nlinarith
  have hp1 : (10591606708171/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21233988421733/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4894553170147/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1107539866003/200000000000:ℝ) := by nlinarith
  have hN : (1960806607833/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (164114424897777/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1960806607833/500000000000:ℝ) (164114424897777/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1427499659/10000000000000:ℝ) ≤ ((1960806607833/500000000000:ℝ)/(164114424897777/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1016 (x : ℝ) (h₁ : (1043/256:ℝ) ≤ x) (h₂ : x ≤ (8369/2048:ℝ)) : (1424080951/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2331650797/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (543029199/2000000000:ℝ) := by nlinarith
  have hc1 : (963365797507/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (963365797507/1000000000000:ℝ) ≤ taylorCos (543029199/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (972939954481/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2331650797/10000000000:ℝ) + taylorErr ≤ (972939954481/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (231058105961/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (231058105961/1000000000000:ℝ) ≤ taylorSin (2331650797/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (33523857421/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (543029199/2000000000:ℝ) + taylorErr ≤ (33523857421/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (963365797507/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (972939954481/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (231058105961/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (33523857421/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12799535694117/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2567577042763/200000000000:ℝ) := by nlinarith
  have hp1 : (10591606708171/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21246682102041/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4894553170147/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (2849082965833/500000000000:ℝ) := by nlinarith
  have hN : (1960806607833/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (16431129676309/50000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1960806607833/500000000000:ℝ) (16431129676309/50000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1424080951/10000000000000:ℝ) ≤ ((1960806607833/500000000000:ℝ)/(16431129676309/50000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1017 (x : ℝ) (h₁ : (1043/256:ℝ) ≤ x) (h₂ : x ≤ (4187/1024:ℝ)) : (1420672477/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2331650797/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1395922517/5000000000:ℝ) := by nlinarith
  have hc1 : (240320120887/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (240320120887/250000000000:ℝ) ≤ taylorCos (1395922517/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (972939954481/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2331650797/10000000000:ℝ) + taylorErr ≤ (972939954481/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (231058105961/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (231058105961/1000000000000:ℝ) ≤ taylorSin (2331650797/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (137785910789/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1395922517/5000000000:ℝ) + taylorErr ≤ (137785910789/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (240320120887/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (972939954481/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (231058105961/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (137785910789/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12799535694117/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2569111023551/200000000000:ℝ) := by nlinarith
  have hp1 : (10591606708171/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1328710986397/62500000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4894553170147/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (2929242454977/500000000000:ℝ) := by nlinarith
  have hN : (1960806607833/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (82254143141641/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1960806607833/500000000000:ℝ) (82254143141641/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1420672477/10000000000000:ℝ) ≤ ((1960806607833/500000000000:ℝ)/(82254143141641/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1018 (x : ℝ) (h₁ : (1043/256:ℝ) ≤ x) (h₂ : x ≤ (131/32:ℝ)) : (1413886087/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2331650797/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2945243113/10000000000:ℝ) := by nlinarith
  have hc1 : (956940333463/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (956940333463/1000000000000:ℝ) ≤ taylorCos (2945243113/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (972939954481/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2331650797/10000000000:ℝ) + taylorErr ≤ (972939954481/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (231058105961/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (231058105961/1000000000000:ℝ) ≤ taylorSin (2331650797/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (290284679541/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2945243113/10000000000:ℝ) + taylorErr ≤ (290284679541/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (956940333463/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (972939954481/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (231058105961/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (290284679541/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12799535694117/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6430447462817/500000000000:ℝ) := by nlinarith
  have hp1 : (10591606708171/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21284763142971/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4894553170147/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (48270630063/7812500000:ℝ) := by nlinarith
  have hN : (1960806607833/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (329805236576397/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1960806607833/500000000000:ℝ) (329805236576397/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1413886087/10000000000000:ℝ) ≤ ((1960806607833/500000000000:ℝ)/(329805236576397/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1019 (x : ℝ) (h₁ : (1043/256:ℝ) ≤ x) (h₂ : x ≤ (4197/1024:ℝ)) : (703570097/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2331650797/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (387330149/1250000000:ℝ) := by nlinarith
  have hc1 : (952375010443/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (952375010443/1000000000000:ℝ) ≤ taylorCos (387330149/1250000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (972939954481/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2331650797/10000000000:ℝ) + taylorErr ≤ (972939954481/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (231058105961/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (231058105961/1000000000000:ℝ) ≤ taylorSin (2331650797/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (152464616021/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (387330149/1250000000:ℝ) + taylorErr ≤ (152464616021/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (952375010443/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (972939954481/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (231058105961/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (152464616021/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12799535694117/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12876234733513/1000000000000:ℝ) := by nlinarith
  have hp1 : (10591606708171/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2131015050359/100000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4894553170147/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (81226097847/12500000000:ℝ) := by nlinarith
  have hN : (1960806607833/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (165297420912527/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1960806607833/500000000000:ℝ) (165297420912527/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (703570097/5000000000000:ℝ) ≤ ((1960806607833/500000000000:ℝ)/(165297420912527/500000000000:ℝ))^2 := by norm_num
  linarith

end Zeta23Ext.Bridge.FourPoint
