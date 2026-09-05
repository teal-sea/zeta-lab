import FourPoint.Base

noncomputable section
open Real
namespace Zeta23Ext.Bridge.FourPoint


theorem wc_1500 (x : ℝ) (h₁ : (655/128:ℝ) ≤ x) (h₂ : x ≤ (335/64:ℝ)) : (640756761/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (368155389/1000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (3681553891/5000000000:ℝ) := by nlinarith
  have hc1 : (74095112303/100000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (74095112303/100000000000:ℝ) ≤ taylorCos (3681553891/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (93299280113/100000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (368155389/1000000000:ℝ) + taylorErr ≤ (93299280113/100000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (179947517093/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (179947517093/500000000000:ℝ) ≤ taylorSin (368155389/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (671558957117/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3681553891/5000000000:ℝ) + taylorErr ≤ (671558957117/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-93299280113/100000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-74095112303/100000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-671558957117/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-179947517093/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (16076118657041/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3288854809227/200000000000:ℝ) := by nlinarith
  have hp1 : (1330297678591/50000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2721525058357/100000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-18276645299581/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-9575350570281/1000000000000:ℝ) := by nlinarith
  have hN : (8642357769151/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (539828297808779/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (8642357769151/1000000000000:ℝ) (539828297808779/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (640756761/2500000000000:ℝ) ≤ ((8642357769151/1000000000000:ℝ)/(539828297808779/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1501 (x : ℝ) (h₁ : (655/128:ℝ) ≤ x) (h₂ : x ≤ (21/4:ℝ)) : (1266297497/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (368155389/1000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (93299280113/100000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (368155389/1000000000:ℝ) + taylorErr ≤ (93299280113/100000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (179947517093/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (179947517093/500000000000:ℝ) ≤ taylorSin (368155389/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (176776695861/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/5000000000:ℝ) + taylorErr ≤ (176776695861/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-93299280113/100000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-88388347351/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-176776695861/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-179947517093/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (16076118657041/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (16493361431347/1000000000000:ℝ) := by nlinarith
  have hp1 : (1330297678591/50000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (545929802751/20000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-9650766670237/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-9575350570281/1000000000000:ℝ) := by nlinarith
  have hN : (8642357769151/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (54306194261009/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (8642357769151/1000000000000:ℝ) (54306194261009/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1266297497/5000000000000:ℝ) ≤ ((8642357769151/1000000000000:ℝ)/(54306194261009/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1502 (x : ℝ) (h₁ : (1313/256:ℝ) ≤ x) (h₂ : x ≤ (21/4:ℝ)) : (3116773877/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (25310683/62500000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (919113853953/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (25310683/62500000:ℝ) + taylorErr ≤ (919113853953/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (393992037797/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (393992037797/1000000000000:ℝ) ≤ taylorSin (25310683/62500000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (176776695861/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/5000000000:ℝ) + taylorErr ≤ (176776695861/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-919113853953/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-88388347351/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-176776695861/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-393992037797/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (322258683919/20000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (16493361431347/1000000000000:ℝ) := by nlinarith
  have hp1 : (3333360404561/125000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (545929802751/20000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-9650766670237/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-5253269834019/500000000000:ℝ) := by nlinarith
  have hN : (1917485162817/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (54306194261009/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1917485162817/200000000000:ℝ) (54306194261009/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (3116773877/10000000000000:ℝ) ≤ ((1917485162817/200000000000:ℝ)/(54306194261009/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1503 (x : ℝ) (h₁ : (165/32:ℝ) ≤ x) (h₂ : x ≤ (21/4:ℝ)) : (2343009541/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (4908738521/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (881921266621/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (4908738521/10000000000:ℝ) + taylorErr ≤ (881921266621/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (471396734543/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (471396734543/1000000000000:ℝ) ≤ taylorSin (4908738521/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (176776695861/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/5000000000:ℝ) + taylorErr ≤ (176776695861/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-881921266621/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-88388347351/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-176776695861/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-471396734543/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (2024854640009/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (16493361431347/1000000000000:ℝ) := by nlinarith
  have hp1 : (837782889189/31250000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (545929802751/20000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-9650766670237/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1263769978303/100000000000:ℝ) := by nlinarith
  have hN : (11755778516409/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (54306194261009/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (11755778516409/1000000000000:ℝ) (54306194261009/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2343009541/5000000000000:ℝ) ≤ ((11755778516409/1000000000000:ℝ)/(54306194261009/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1504 (x : ℝ) (h₁ : (21/4:ℝ) ≤ x) (h₂ : x ≤ (2693/512:ℝ)) : (11636772221/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1886796369/2500000000:ℝ) ≤ Real.pi * ((11/2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((11/2:ℝ) - x) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * ((11/2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((11/2:ℝ) - x)) ≤ (728464392667/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1886796369/2500000000:ℝ) + taylorErr ≤ (728464392667/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (685083665477/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((11/2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (685083665477/1000000000000:ℝ) ≤ taylorSin (1886796369/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((11/2:ℝ) - x)) ≤ (176776695861/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/5000000000:ℝ) + taylorErr ≤ (176776695861/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((11/2:ℝ) - x)) := by
    have h := (trig_shift (11/2:ℝ) (x - (11/2:ℝ))).1
    rw [show (11/2:ℝ) + (x - (11/2:ℝ)) = x by ring, cs_h11.1, cs_h11.2] at h
    rw [h, cos_flip (11/2:ℝ) x, sin_flip (11/2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((11/2:ℝ) - x)) := by
    have h := (trig_shift (11/2:ℝ) (x - (11/2:ℝ))).2
    rw [show (11/2:ℝ) + (x - (11/2:ℝ)) = x by ring, cs_h11.1, cs_h11.2] at h
    rw [h, cos_flip (11/2:ℝ) x, sin_flip (11/2:ℝ) x]; ring
  have hcxl : (-176776695861/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-685083665477/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-728464392667/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-88388347351/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (8246680715673/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3304808209421/200000000000:ℝ) := by nlinarith
  have hp1 : (5459297954279/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (6836816214697/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-19921508686461/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2412691619377/125000000000:ℝ) := by nlinarith
  have hN : (4648606542893/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (272543932526411/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4648606542893/250000000000:ℝ) (272543932526411/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (11636772221/10000000000000:ℝ) ≤ ((4648606542893/250000000000:ℝ)/(272543932526411/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1505 (x : ℝ) (h₁ : (21/4:ℝ) ≤ x) (h₂ : x ≤ (675/128:ℝ)) : (5758172129/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1423534171/2000000000:ℝ) ≤ Real.pi * ((11/2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((11/2:ℝ) - x) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * ((11/2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((11/2:ℝ) - x)) ≤ (151441769757/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1423534171/2000000000:ℝ) + taylorErr ≤ (151441769757/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (65317284063/100000000000:ℝ) ≤ Real.sin (Real.pi * ((11/2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (65317284063/100000000000:ℝ) ≤ taylorSin (1423534171/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((11/2:ℝ) - x)) ≤ (176776695861/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/5000000000:ℝ) + taylorErr ≤ (176776695861/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((11/2:ℝ) - x)) := by
    have h := (trig_shift (11/2:ℝ) (x - (11/2:ℝ))).1
    rw [show (11/2:ℝ) + (x - (11/2:ℝ)) = x by ring, cs_h11.1, cs_h11.2] at h
    rw [h, cos_flip (11/2:ℝ) x, sin_flip (11/2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((11/2:ℝ) - x)) := by
    have h := (trig_shift (11/2:ℝ) (x - (11/2:ℝ))).2
    rw [show (11/2:ℝ) + (x - (11/2:ℝ)) = x by ring, cs_h11.1, cs_h11.2] at h
    rw [h, cos_flip (11/2:ℝ) x, sin_flip (11/2:ℝ) x]; ring
  have hcxl : (-176776695861/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-65317284063/100000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-151441769757/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-88388347351/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (8246680715673/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3313398501833/200000000000:ℝ) := by nlinarith
  have hp1 : (5459297954279/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (685458736713/25000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-20761416836643/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2412691619377/125000000000:ℝ) := by nlinarith
  have hN : (4648606542893/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (547930481597459/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4648606542893/250000000000:ℝ) (547930481597459/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (5758172129/5000000000000:ℝ) ≤ ((4648606542893/250000000000:ℝ)/(547930481597459/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1506 (x : ℝ) (h₁ : (21/4:ℝ) ≤ x) (h₂ : x ≤ (1353/256:ℝ)) : (11414358387/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (3374757733/5000000000:ℝ) ≤ Real.pi * ((11/2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((11/2:ℝ) - x) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * ((11/2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((11/2:ℝ) - x)) ≤ (780737230859/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (3374757733/5000000000:ℝ) + taylorErr ≤ (780737230859/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (24994379433/40000000000:ℝ) ≤ Real.sin (Real.pi * ((11/2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (24994379433/40000000000:ℝ) ≤ taylorSin (3374757733/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((11/2:ℝ) - x)) ≤ (176776695861/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/5000000000:ℝ) + taylorErr ≤ (176776695861/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((11/2:ℝ) - x)) := by
    have h := (trig_shift (11/2:ℝ) (x - (11/2:ℝ))).1
    rw [show (11/2:ℝ) + (x - (11/2:ℝ)) = x by ring, cs_h11.1, cs_h11.2] at h
    rw [h, cos_flip (11/2:ℝ) x, sin_flip (11/2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((11/2:ℝ) - x)) := by
    have h := (trig_shift (11/2:ℝ) (x - (11/2:ℝ))).2
    rw [show (11/2:ℝ) + (x - (11/2:ℝ)) = x by ring, cs_h11.1, cs_h11.2] at h
    rw [h, cos_flip (11/2:ℝ) x, sin_flip (11/2:ℝ) x]; ring
  have hcxl : (-176776695861/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-24994379433/40000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-780737230859/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-88388347351/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (8246680715673/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (664152321923/40000000000:ℝ) := by nlinarith
  have hp1 : (5459297954279/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (27479279134007/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-21454096297087/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2412691619377/125000000000:ℝ) := by nlinarith
  have hN : (4648606542893/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (550372883394641/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4648606542893/250000000000:ℝ) (550372883394641/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (11414358387/10000000000000:ℝ) ≤ ((4648606542893/250000000000:ℝ)/(550372883394641/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1507 (x : ℝ) (h₁ : (21/4:ℝ) ≤ x) (h₂ : x ≤ (85/16:ℝ)) : (1397593481/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (235619449/400000000:ℝ) ≤ Real.pi * ((11/2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((11/2:ℝ) - x) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * ((11/2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((11/2:ℝ) - x)) ≤ (207867403647/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (235619449/400000000:ℝ) + taylorErr ≤ (207867403647/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (555570230717/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((11/2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (555570230717/1000000000000:ℝ) ≤ taylorSin (235619449/400000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((11/2:ℝ) - x)) ≤ (176776695861/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/5000000000:ℝ) + taylorErr ≤ (176776695861/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((11/2:ℝ) - x)) := by
    have h := (trig_shift (11/2:ℝ) (x - (11/2:ℝ))).1
    rw [show (11/2:ℝ) + (x - (11/2:ℝ)) = x by ring, cs_h11.1, cs_h11.2] at h
    rw [h, cos_flip (11/2:ℝ) x, sin_flip (11/2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((11/2:ℝ) - x)) := by
    have h := (trig_shift (11/2:ℝ) (x - (11/2:ℝ))).2
    rw [show (11/2:ℝ) + (x - (11/2:ℝ)) = x by ring, cs_h11.1, cs_h11.2] at h
    rw [h, cos_flip (11/2:ℝ) x, sin_flip (11/2:ℝ) x]; ring
  have hcxl : (-176776695861/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-555570230717/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-207867403647/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-88388347351/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (8246680715673/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (4172427743049/250000000000:ℝ) := by nlinarith
  have hp1 : (5459297954279/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (431585130523/15625000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2870799377103/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2412691619377/125000000000:ℝ) := by nlinarith
  have hN : (4648606542893/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (3475580654193/6250000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4648606542893/250000000000:ℝ) (3475580654193/6250000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1397593481/1250000000000:ℝ) ≤ ((4648606542893/250000000000:ℝ)/(3475580654193/6250000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1508 (x : ℝ) (h₁ : (21/4:ℝ) ≤ x) (h₂ : x ≤ (681/128:ℝ)) : (2223020503/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (5645049299/10000000000:ℝ) ≤ Real.pi * ((11/2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((11/2:ℝ) - x) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * ((11/2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((11/2:ℝ) - x)) ≤ (211213391883/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (5645049299/10000000000:ℝ) + taylorErr ≤ (211213391883/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (534997617589/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((11/2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (534997617589/1000000000000:ℝ) ≤ taylorSin (5645049299/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((11/2:ℝ) - x)) ≤ (176776695861/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/5000000000:ℝ) + taylorErr ≤ (176776695861/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((11/2:ℝ) - x)) := by
    have h := (trig_shift (11/2:ℝ) (x - (11/2:ℝ))).1
    rw [show (11/2:ℝ) + (x - (11/2:ℝ)) = x by ring, cs_h11.1, cs_h11.2] at h
    rw [h, cos_flip (11/2:ℝ) x, sin_flip (11/2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((11/2:ℝ) - x)) := by
    have h := (trig_shift (11/2:ℝ) (x - (11/2:ℝ))).2
    rw [show (11/2:ℝ) + (x - (11/2:ℝ)) = x by ring, cs_h11.1, cs_h11.2] at h
    rw [h, cos_flip (11/2:ℝ) x, sin_flip (11/2:ℝ) x]; ring
  have hcxl : (-176776695861/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-534997617589/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-211213391883/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-88388347351/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (8246680715673/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (8357127332401/500000000000:ℝ) := by nlinarith
  have hp1 : (5459297954279/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (27662068130463/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-4674079389067/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2412691619377/125000000000:ℝ) := by nlinarith
  have hN : (4648606542893/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (557732617999711/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4648606542893/250000000000:ℝ) (557732617999711/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2223020503/2000000000000:ℝ) ≤ ((4648606542893/250000000000:ℝ)/(557732617999711/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1509 (x : ℝ) (h₁ : (21/4:ℝ) ≤ x) (h₂ : x ≤ (1373/256:ℝ)) : (2152508603/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2147573103/5000000000:ℝ) ≤ Real.pi * ((11/2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((11/2:ℝ) - x) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * ((11/2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((11/2:ℝ) - x)) ≤ (227291996339/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2147573103/5000000000:ℝ) + taylorErr ≤ (227291996339/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (104107389457/250000000000:ℝ) ≤ Real.sin (Real.pi * ((11/2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (104107389457/250000000000:ℝ) ≤ taylorSin (2147573103/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((11/2:ℝ) - x)) ≤ (176776695861/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/5000000000:ℝ) + taylorErr ≤ (176776695861/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((11/2:ℝ) - x)) := by
    have h := (trig_shift (11/2:ℝ) (x - (11/2:ℝ))).1
    rw [show (11/2:ℝ) + (x - (11/2:ℝ)) = x by ring, cs_h11.1, cs_h11.2] at h
    rw [h, cos_flip (11/2:ℝ) x, sin_flip (11/2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((11/2:ℝ) - x)) := by
    have h := (trig_shift (11/2:ℝ) (x - (11/2:ℝ))).2
    rw [show (11/2:ℝ) + (x - (11/2:ℝ)) = x by ring, cs_h11.1, cs_h11.2] at h
    rw [h, cos_flip (11/2:ℝ) x, sin_flip (11/2:ℝ) x]; ring
  have hcxl : (-176776695861/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-104107389457/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-227291996339/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-88388347351/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (8246680715673/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2106155621767/125000000000:ℝ) := by nlinarith
  have hp1 : (5459297954279/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2788547690391/100000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1267629142871/50000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2412691619377/125000000000:ℝ) := by nlinarith
  have hN : (4648606542893/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (113358822479379/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4648606542893/250000000000:ℝ) (113358822479379/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2152508603/2000000000000:ℝ) ≤ ((4648606542893/250000000000:ℝ)/(113358822479379/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1510 (x : ℝ) (h₁ : (21/4:ℝ) ≤ x) (h₂ : x ≤ (345/64:ℝ)) : (2636362983/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (859029241/2500000000:ℝ) ≤ Real.pi * ((11/2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((11/2:ℝ) - x) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * ((11/2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((11/2:ℝ) - x)) ≤ (470772033737/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (859029241/2500000000:ℝ) + taylorErr ≤ (470772033737/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (336889851049/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((11/2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (336889851049/1000000000000:ℝ) ≤ taylorSin (859029241/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((11/2:ℝ) - x)) ≤ (176776695861/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/5000000000:ℝ) + taylorErr ≤ (176776695861/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((11/2:ℝ) - x)) := by
    have h := (trig_shift (11/2:ℝ) (x - (11/2:ℝ))).1
    rw [show (11/2:ℝ) + (x - (11/2:ℝ)) = x by ring, cs_h11.1, cs_h11.2] at h
    rw [h, cos_flip (11/2:ℝ) x, sin_flip (11/2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((11/2:ℝ) - x)) := by
    have h := (trig_shift (11/2:ℝ) (x - (11/2:ℝ))).2
    rw [show (11/2:ℝ) + (x - (11/2:ℝ)) = x by ring, cs_h11.1, cs_h11.2] at h
    rw [h, cos_flip (11/2:ℝ) x, sin_flip (11/2:ℝ) x]; ring
  have hcxl : (-176776695861/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-336889851049/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-470772033737/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-88388347351/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (8246680715673/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (8467573949129/500000000000:ℝ) := by nlinarith
  have hp1 : (5459297954279/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (28027646123377/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-26389263932727/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2412691619377/125000000000:ℝ) := by nlinarith
  have hN : (4648606542893/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (114519693734349/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4648606542893/250000000000:ℝ) (114519693734349/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2636362983/2500000000000:ℝ) ≤ ((4648606542893/250000000000:ℝ)/(114519693734349/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1511 (x : ℝ) (h₁ : (21/4:ℝ) ≤ x) (h₂ : x ≤ (1393/256:ℝ)) : (5078306397/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (368155389/2000000000:ℝ) ≤ Real.pi * ((11/2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((11/2:ℝ) - x) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * ((11/2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((11/2:ℝ) - x)) ≤ (491552744851/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (368155389/2000000000:ℝ) + taylorErr ≤ (491552744851/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (183039885647/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((11/2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (183039885647/1000000000000:ℝ) ≤ taylorSin (368155389/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((11/2:ℝ) - x)) ≤ (176776695861/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/5000000000:ℝ) + taylorErr ≤ (176776695861/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((11/2:ℝ) - x)) := by
    have h := (trig_shift (11/2:ℝ) (x - (11/2:ℝ))).1
    rw [show (11/2:ℝ) + (x - (11/2:ℝ)) = x by ring, cs_h11.1, cs_h11.2] at h
    rw [h, cos_flip (11/2:ℝ) x, sin_flip (11/2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((11/2:ℝ) - x)) := by
    have h := (trig_shift (11/2:ℝ) (x - (11/2:ℝ))).2
    rw [show (11/2:ℝ) + (x - (11/2:ℝ)) = x by ring, cs_h11.1, cs_h11.2] at h
    rw [h, cos_flip (11/2:ℝ) x, sin_flip (11/2:ℝ) x]; ring
  have hcxl : (-176776695861/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-183039885647/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-491552744851/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-88388347351/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (8246680715673/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (8547340950099/500000000000:ℝ) := by nlinarith
  have hp1 : (5459297954279/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (14145837336907/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2781370068469/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2412691619377/125000000000:ℝ) := by nlinarith
  have hN : (4648606542893/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (116691259707583/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4648606542893/250000000000:ℝ) (116691259707583/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (5078306397/5000000000000:ℝ) ≤ ((4648606542893/250000000000:ℝ)/(116691259707583/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1512 (x : ℝ) (h₁ : (21/4:ℝ) ≤ x) (h₂ : x ≤ (175/32:ℝ)) : (9954658577/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/1250000000:ℝ) ≤ Real.pi * ((11/2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((11/2:ℝ) - x) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * ((11/2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((11/2:ℝ) - x)) ≤ (995184728937/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/1250000000:ℝ) + taylorErr ≤ (995184728937/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (98017138043/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((11/2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (98017138043/1000000000000:ℝ) ≤ taylorSin (122718463/1250000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((11/2:ℝ) - x)) ≤ (176776695861/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/5000000000:ℝ) + taylorErr ≤ (176776695861/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((11/2:ℝ) - x)) := by
    have h := (trig_shift (11/2:ℝ) (x - (11/2:ℝ))).1
    rw [show (11/2:ℝ) + (x - (11/2:ℝ)) = x by ring, cs_h11.1, cs_h11.2] at h
    rw [h, cos_flip (11/2:ℝ) x, sin_flip (11/2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((11/2:ℝ) - x)) := by
    have h := (trig_shift (11/2:ℝ) (x - (11/2:ℝ))).2
    rw [show (11/2:ℝ) + (x - (11/2:ℝ)) = x by ring, cs_h11.1, cs_h11.2] at h
    rw [h, cos_flip (11/2:ℝ) x, sin_flip (11/2:ℝ) x]; ring
  have hcxl : (-176776695861/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-98017138043/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-995184728937/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-88388347351/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (8246680715673/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6711165947/390625000:ℝ) := by nlinarith
  have hp1 : (5459297954279/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (28433843893281/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-7074231806893/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2412691619377/125000000000:ℝ) := by nlinarith
  have hN : (4648606542893/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (58934498981131/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4648606542893/250000000000:ℝ) (58934498981131/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (9954658577/10000000000000:ℝ) ≤ ((4648606542893/250000000000:ℝ)/(58934498981131/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1513 (x : ℝ) (h₁ : (21/4:ℝ) ≤ x) (h₂ : x ≤ (11/2:ℝ)) : (2432490771/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * ((11/2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((11/2:ℝ) - x) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * ((11/2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((11/2:ℝ) - x)) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * ((11/2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((11/2:ℝ) - x)) ≤ (176776695861/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/5000000000:ℝ) + taylorErr ≤ (176776695861/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((11/2:ℝ) - x)) := by
    have h := (trig_shift (11/2:ℝ) (x - (11/2:ℝ))).1
    rw [show (11/2:ℝ) + (x - (11/2:ℝ)) = x by ring, cs_h11.1, cs_h11.2] at h
    rw [h, cos_flip (11/2:ℝ) x, sin_flip (11/2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((11/2:ℝ) - x)) := by
    have h := (trig_shift (11/2:ℝ) (x - (11/2:ℝ))).2
    rw [show (11/2:ℝ) + (x - (11/2:ℝ)) = x by ring, cs_h11.1, cs_h11.2] at h
    rw [h, cos_flip (11/2:ℝ) x, sin_flip (11/2:ℝ) x]; ring
  have hcxl : (-176776695861/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (1131/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-500000001131/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-88388347351/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (8246680715673/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2159844949343/125000000000:ℝ) := by nlinarith
  have hp1 : (5459297954279/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (14298161500621/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-28596323065927/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2412691619377/125000000000:ℝ) := by nlinarith
  have hN : (4648606542893/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (149027766566479/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4648606542893/250000000000:ℝ) (149027766566479/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2432490771/2500000000000:ℝ) ≤ ((4648606542893/250000000000:ℝ)/(149027766566479/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1514 (x : ℝ) (h₁ : (11/2:ℝ) ≤ x) (h₂ : x ≤ (355/64:ℝ)) : (21764380703/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * (x - (11/2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (11/2:ℝ)) ≤ (1472621557/10000000000:ℝ) := by nlinarith
  have hc1 : (989176507693/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (11/2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (989176507693/1000000000000:ℝ) ≤ taylorCos (1472621557/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (11/2:ℝ))) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (11/2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (11/2:ℝ))) ≤ (7336523839/50000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1472621557/10000000000:ℝ) + taylorErr ≤ (7336523839/50000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (11/2:ℝ))) := by
    have h := (trig_shift (11/2:ℝ) (x - (11/2:ℝ))).1
    rw [show (11/2:ℝ) + (x - (11/2:ℝ)) = x by ring, cs_h11.1, cs_h11.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (11/2:ℝ))) := by
    have h := (trig_shift (11/2:ℝ) (x - (11/2:ℝ))).2
    rw [show (11/2:ℝ) + (x - (11/2:ℝ)) = x by ring, cs_h11.1, cs_h11.2] at h
    rw [h]; ring
  have hcxl : (-1131/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (7336523839/50000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-500000001131/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-989176507693/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (17278759594743/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (17426021750381/1000000000000:ℝ) := by nlinarith
  have hp1 : (28596322617651/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1802502603949/62500000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-28840041728421/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2828681053979/100000000000:ℝ) := by nlinarith
  have hN : (3535851317191/125000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (18947889627797/31250000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3535851317191/125000000000:ℝ) (18947889627797/31250000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (21764380703/10000000000000:ℝ) ≤ ((3535851317191/125000000000:ℝ)/(18947889627797/31250000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1515 (x : ℝ) (h₁ : (11/2:ℝ) ≤ x) (h₂ : x ≤ (89/16:ℝ)) : (10578448877/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * (x - (11/2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (11/2:ℝ)) ≤ (1963495409/10000000000:ℝ) := by nlinarith
  have hc1 : (980785278131/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (11/2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (980785278131/1000000000000:ℝ) ≤ taylorCos (1963495409/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (11/2:ℝ))) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (11/2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (11/2:ℝ))) ≤ (24386290541/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1963495409/10000000000:ℝ) + taylorErr ≤ (24386290541/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (11/2:ℝ))) := by
    have h := (trig_shift (11/2:ℝ) (x - (11/2:ℝ))).1
    rw [show (11/2:ℝ) + (x - (11/2:ℝ)) = x by ring, cs_h11.1, cs_h11.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (11/2:ℝ))) := by
    have h := (trig_shift (11/2:ℝ) (x - (11/2:ℝ))).2
    rw [show (11/2:ℝ) + (x - (11/2:ℝ)) = x by ring, cs_h11.1, cs_h11.2] at h
    rw [h]; ring
  have hcxl : (-1131/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (24386290541/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-500000001131/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-980785278131/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (17278759594743/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (8737554567797/500000000000:ℝ) := by nlinarith
  have hp1 : (28596322617651/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (14460640608583/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-14460640641293/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-7011713058019/250000000000:ℝ) := by nlinarith
  have hN : (14023426114907/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (304879439300921/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (14023426114907/500000000000:ℝ) (304879439300921/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (10578448877/5000000000000:ℝ) ≤ ((14023426114907/500000000000:ℝ)/(304879439300921/500000000000:ℝ))^2 := by norm_num
  linarith

end Zeta23Ext.Bridge.FourPoint
