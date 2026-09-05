import FourPoint.Base

noncomputable section
open Real
namespace Zeta23Ext.Bridge.FourPoint


theorem wc_240 (x : ℝ) (h₁ : (4107/2048:ℝ) ≤ x) (h₂ : x ≤ (257/128:ℝ)) : (179073511/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (84368943/5000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (245436927/10000000000:ℝ) := by nlinarith
  have hc1 : (62481176027/62500000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (62481176027/62500000000:ℝ) ≤ taylorCos (245436927/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (999857643269/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (84368943/5000000000:ℝ) + taylorErr ≤ (999857643269/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (8436492809/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (8436492809/500000000000:ℝ) ≤ taylorSin (84368943/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (999857643269/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (8436492809/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (24541230879/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3150029547923/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3153864499893/500000000000:ℝ) := by nlinarith
  have hp1 : (10426588866361/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5219641343267/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (87963841993/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (128096423311/500000000000:ℝ) := by nlinarith
  have hN : (74350596981/100000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (78574890269483/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (74350596981/100000000000:ℝ) (78574890269483/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (179073511/2000000000000:ℝ) ≤ ((74350596981/100000000000:ℝ)/(78574890269483/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_241 (x : ℝ) (h₁ : (257/128:ℝ) ≤ x) (h₂ : x ≤ (4117/2048:ℝ)) : (708136113/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/5000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (161067983/5000000000:ℝ) := by nlinarith
  have hc1 : (499740592351/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (499740592351/500000000000:ℝ) ≤ taylorCos (161067983/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (999698820959/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/5000000000:ℝ) + taylorErr ≤ (999698820959/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (4908245251/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (4908245251/200000000000:ℝ) ≤ taylorSin (122718463/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (2:ℝ))) ≤ (1288321109/40000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (161067983/5000000000:ℝ) + taylorErr ≤ (1288321109/40000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h]; ring
  have hcxl : (499740592351/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (999698820959/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (4908245251/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1288321109/40000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1261545799957/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3157699451863/500000000000:ℝ) := by nlinarith
  have hp1 : (10439282546499/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2612994091711/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (256192794913/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (67327508921/200000000000:ℝ) := by nlinarith
  have hN : (662843640097/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (1230758228537/15625000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (662843640097/1000000000000:ℝ) (1230758228537/15625000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (708136113/10000000000000:ℝ) ≤ ((662843640097/1000000000000:ℝ)/(1230758228537/15625000000:ℝ))^2 := by norm_num
  linarith

theorem wc_242 (x : ℝ) (h₁ : (257/128:ℝ) ≤ x) (h₂ : x ≤ (2061/1024:ℝ)) : (543159341/10000000000000:ℝ) ≤ wfun x := by
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

theorem wc_243 (x : ℝ) (h₁ : (257/128:ℝ) ≤ x) (h₂ : x ≤ (1033/512:ℝ)) : (27945219/1000000000000:ℝ) ≤ wfun x := by
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

theorem wc_244 (x : ℝ) (h₁ : (257/128:ℝ) ≤ x) (h₂ : x ≤ (519/256:ℝ)) : (13164037/10000000000000:ℝ) ≤ wfun x := by
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

theorem wc_245 (x : ℝ) (h₁ : (4117/2048:ℝ) ≤ x) (h₂ : x ≤ (2061/1024:ℝ)) : (543159341/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (64427193/2000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (79767001/2000000000:ℝ) := by nlinarith
  have hc1 : (249801189089/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (249801189089/250000000000:ℝ) ≤ taylorCos (79767001/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (99948118923/100000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (64427193/2000000000:ℝ) + taylorErr ≤ (99948118923/100000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (32208023101/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (32208023101/1000000000000:ℝ) ≤ taylorSin (64427193/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (99948118923/100000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (32208023101/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (7974585973/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (252615956149/40000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1264613761533/200000000000:ℝ) := by nlinarith
  have hp1 : (10451976226639/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10464670047153/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (168318745879/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (417257054851/1000000000000:ℝ) := by nlinarith
  have hN : (116389540301/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (78962398292933/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (116389540301/200000000000:ℝ) (78962398292933/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (543159341/10000000000000:ℝ) ≤ ((116389540301/200000000000:ℝ)/(78962398292933/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_246 (x : ℝ) (h₁ : (2061/1024:ℝ) ≤ x) (h₂ : x ≤ (1033/512:ℝ)) : (27945219/1000000000000:ℝ) ≤ wfun x := by
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

theorem wc_247 (x : ℝ) (h₁ : (1033/512:ℝ) ≤ x) (h₂ : x ≤ (2071/1024:ℝ)) : (103168503/10000000000000:ℝ) ≤ wfun x := by
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

theorem wc_248 (x : ℝ) (h₁ : (1033/512:ℝ) ≤ x) (h₂ : x ≤ (519/256:ℝ)) : (13164037/10000000000000:ℝ) ≤ wfun x := by
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

theorem wc_249 (x : ℝ) (h₁ : (2071/1024:ℝ) ≤ x) (h₂ : x ≤ (519/256:ℝ)) : (13164037/10000000000000:ℝ) ≤ wfun x := by
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

theorem wc_250 (x : ℝ) (h₁ : (1043/512:ℝ) ≤ x) (h₂ : x ≤ (131/64:ℝ)) : (21355581/2500000000000:ℝ) ≤ wfun x := by
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

theorem wc_251 (x : ℝ) (h₁ : (1043/512:ℝ) ≤ x) (h₂ : x ≤ (1053/512:ℝ)) : (83791953/10000000000000:ℝ) ≤ wfun x := by
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

theorem wc_252 (x : ℝ) (h₁ : (1043/512:ℝ) ≤ x) (h₂ : x ≤ (529/256:ℝ)) : (1284381/156250000000:ℝ) ≤ wfun x := by
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

theorem wc_253 (x : ℝ) (h₁ : (131/64:ℝ) ≤ x) (h₂ : x ≤ (529/256:ℝ)) : (94460693/2000000000000:ℝ) ≤ wfun x := by
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

theorem wc_254 (x : ℝ) (h₁ : (131/64:ℝ) ≤ x) (h₂ : x ≤ (1063/512:ℝ)) : (115843823/2500000000000:ℝ) ≤ wfun x := by
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

theorem wc_255 (x : ℝ) (h₁ : (131/64:ℝ) ≤ x) (h₂ : x ≤ (267/128:ℝ)) : (18186303/400000000000:ℝ) ≤ wfun x := by
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

theorem wc_256 (x : ℝ) (h₁ : (131/64:ℝ) ≤ x) (h₂ : x ≤ (539/256:ℝ)) : (437829947/10000000000000:ℝ) ≤ wfun x := by
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

theorem wc_257 (x : ℝ) (h₁ : (131/64:ℝ) ≤ x) (h₂ : x ≤ (17/8:ℝ)) : (42177537/1000000000000:ℝ) ≤ wfun x := by
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

theorem wc_258 (x : ℝ) (h₁ : (131/64:ℝ) ≤ x) (h₂ : x ≤ (277/128:ℝ)) : (12244337/312500000000:ℝ) ≤ wfun x := by
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

theorem wc_259 (x : ℝ) (h₁ : (131/64:ℝ) ≤ x) (h₂ : x ≤ (141/64:ℝ)) : (182240171/5000000000000:ℝ) ≤ wfun x := by
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

theorem wc_260 (x : ℝ) (h₁ : (131/64:ℝ) ≤ x) (h₂ : x ≤ (9/4:ℝ)) : (167375901/5000000000000:ℝ) ≤ wfun x := by
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

theorem wc_261 (x : ℝ) (h₁ : (1053/512:ℝ) ≤ x) (h₂ : x ≤ (1063/512:ℝ)) : (291856019/2500000000000:ℝ) ≤ wfun x := by
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

theorem wc_262 (x : ℝ) (h₁ : (1053/512:ℝ) ≤ x) (h₂ : x ≤ (267/128:ℝ)) : (1145460727/10000000000000:ℝ) ≤ wfun x := by
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

theorem wc_263 (x : ℝ) (h₁ : (529/256:ℝ) ≤ x) (h₂ : x ≤ (2131/1024:ℝ)) : (54451693/250000000000:ℝ) ≤ wfun x := by
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

theorem wc_264 (x : ℝ) (h₁ : (529/256:ℝ) ≤ x) (h₂ : x ≤ (267/128:ℝ)) : (269688311/1250000000000:ℝ) ≤ wfun x := by
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

theorem wc_265 (x : ℝ) (h₁ : (529/256:ℝ) ≤ x) (h₂ : x ≤ (1073/512:ℝ)) : (264638553/1250000000000:ℝ) ≤ wfun x := by
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

theorem wc_266 (x : ℝ) (h₁ : (529/256:ℝ) ≤ x) (h₂ : x ≤ (539/256:ℝ)) : (259706701/1250000000000:ℝ) ≤ wfun x := by
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

theorem wc_267 (x : ℝ) (h₁ : (529/256:ℝ) ≤ x) (h₂ : x ≤ (17/8:ℝ)) : (2001469121/10000000000000:ℝ) ≤ wfun x := by
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

theorem wc_268 (x : ℝ) (h₁ : (2121/1024:ℝ) ≤ x) (h₂ : x ≤ (267/128:ℝ)) : (1392763463/5000000000000:ℝ) ≤ wfun x := by
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

theorem wc_269 (x : ℝ) (h₁ : (1063/512:ℝ) ≤ x) (h₂ : x ≤ (1073/512:ℝ)) : (343008739/1000000000000:ℝ) ≤ wfun x := by
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

theorem wc_270 (x : ℝ) (h₁ : (1063/512:ℝ) ≤ x) (h₂ : x ≤ (539/256:ℝ)) : (3366163659/10000000000000:ℝ) ≤ wfun x := by
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

theorem wc_271 (x : ℝ) (h₁ : (267/128:ℝ) ≤ x) (h₂ : x ≤ (539/256:ℝ)) : (2485973639/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1349903093/5000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (1656699251/5000000000:ℝ) := by nlinarith
  have hc1 : (945607323113/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (945607323113/1000000000000:ℝ) ≤ taylorCos (1656699251/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (240944017019/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1349903093/5000000000:ℝ) + taylorErr ≤ (240944017019/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (266712755147/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (266712755147/1000000000000:ℝ) ≤ taylorSin (1349903093/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (240944017019/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (266712755147/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (8132757361/25000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6553165925847/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6614525157363/1000000000000:ℝ) := by nlinarith
  have hp1 : (2169096062191/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10947029898913/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2892627934627/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (3561181519659/1000000000000:ℝ) := by nlinarith
  have hN : (1928851866551/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (86503886114777/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1928851866551/1000000000000:ℝ) (86503886114777/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2485973639/5000000000000:ℝ) ≤ ((1928851866551/1000000000000:ℝ)/(86503886114777/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_272 (x : ℝ) (h₁ : (267/128:ℝ) ≤ x) (h₂ : x ≤ (17/8:ℝ)) : (4789633321/10000000000000:ℝ) ≤ wfun x := by
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

theorem wc_273 (x : ℝ) (h₁ : (267/128:ℝ) ≤ x) (h₂ : x ≤ (549/256:ℝ)) : (4615617497/10000000000000:ℝ) ≤ wfun x := by
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

theorem wc_274 (x : ℝ) (h₁ : (267/128:ℝ) ≤ x) (h₂ : x ≤ (277/128:ℝ)) : (1112362433/2500000000000:ℝ) ≤ wfun x := by
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

theorem wc_275 (x : ℝ) (h₁ : (267/128:ℝ) ≤ x) (h₂ : x ≤ (141/64:ℝ)) : (129343671/312500000000:ℝ) ≤ wfun x := by
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

theorem wc_276 (x : ℝ) (h₁ : (539/256:ℝ) ≤ x) (h₂ : x ≤ (549/256:ℝ)) : (4243616393/5000000000000:ℝ) ≤ wfun x := by
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

theorem wc_277 (x : ℝ) (h₁ : (539/256:ℝ) ≤ x) (h₂ : x ≤ (277/128:ℝ)) : (2045420557/2500000000000:ℝ) ≤ wfun x := by
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

theorem wc_278 (x : ℝ) (h₁ : (17/8:ℝ) ≤ x) (h₂ : x ≤ (141/64:ℝ)) : (48584483/40000000000:ℝ) ≤ wfun x := by
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

theorem wc_279 (x : ℝ) (h₁ : (17/8:ℝ) ≤ x) (h₂ : x ≤ (9/4:ℝ)) : (2788858101/2500000000000:ℝ) ≤ wfun x := by
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

theorem wc_280 (x : ℝ) (h₁ : (141/64:ℝ) ≤ x) (h₂ : x ≤ (71/32:ℝ)) : (39186989529/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (6381360077/10000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (687223393/1000000000:ℝ) := by nlinarith
  have hc1 : (38650522553/50000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (38650522553/50000000000:ℝ) ≤ taylorCos (687223393/1000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (803207533769/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (6381360077/10000000000:ℝ) + taylorErr ≤ (803207533769/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (595699302181/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (595699302181/1000000000000:ℝ) ≤ taylorSin (6381360077/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (803207533769/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (595699302181/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (317196643223/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (346066065747/50000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6970408700153/1000000000000:ℝ) := by nlinarith
  have hp1 : (11454776957639/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (461440666611/40000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (426475165019/62500000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (365918576239/50000000000:ℝ) := by nlinarith
  have hN : (1204079021307/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (48086597447169/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1204079021307/200000000000:ℝ) (48086597447169/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (39186989529/10000000000000:ℝ) ≤ ((1204079021307/200000000000:ℝ)/(48086597447169/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_281 (x : ℝ) (h₁ : (71/32:ℝ) ≤ x) (h₂ : x ≤ (9/4:ℝ)) : (21886858333/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (6872233929/10000000000:ℝ) ≤ Real.pi * (x - (2:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (2:ℝ)) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (2:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (2:ℝ))) ≤ (24156576739/31250000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (6872233929/10000000000:ℝ) + taylorErr ≤ (24156576739/31250000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (158598320461/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (2:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (158598320461/250000000000:ℝ) ≤ taylorSin (6872233929/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (24156576739/31250000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (158598320461/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (176776695861/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (871301087519/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3534291735289/500000000000:ℝ) := by nlinarith
  have hp1 : (11536016510529/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (11698495773237/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (7318371373521/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (8272085717347/1000000000000:ℝ) := by nlinarith
  have hN : (6545360917873/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (49464872280529/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (6545360917873/1000000000000:ℝ) (49464872280529/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (21886858333/5000000000000:ℝ) ≤ ((6545360917873/1000000000000:ℝ)/(49464872280529/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_282 (x : ℝ) (h₁ : (9/4:ℝ) ≤ x) (h₂ : x ≤ (73/32:ℝ)) : (27652304943/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (6872233929/10000000000:ℝ) ≤ Real.pi * ((5/2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((5/2:ℝ) - x) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * ((5/2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((5/2:ℝ) - x)) ≤ (24156576739/31250000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (6872233929/10000000000:ℝ) + taylorErr ≤ (24156576739/31250000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (158598320461/250000000000:ℝ) ≤ Real.sin (Real.pi * ((5/2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (158598320461/250000000000:ℝ) ≤ taylorSin (6872233929/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (158598320461/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (176776695861/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (88388347351/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (24156576739/31250000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7068583470577/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3583379120501/500000000000:ℝ) := by nlinarith
  have hp1 : (1462311952039/125000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5930487440599/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (8272085552149/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1833731519469/200000000000:ℝ) := by nlinarith
  have hN : (1512995753741/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (101724847369941/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1512995753741/200000000000:ℝ) (101724847369941/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (27652304943/5000000000000:ℝ) ≤ ((1512995753741/200000000000:ℝ)/(101724847369941/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_283 (x : ℝ) (h₁ : (9/4:ℝ) ≤ x) (h₂ : x ≤ (5/2:ℝ)) : (38217750111/10000000000000:ℝ) ≤ wfun x := by
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

theorem wc_284 (x : ℝ) (h₁ : (5/2:ℝ) ≤ x) (h₂ : x ≤ (11/4:ℝ)) : (38423148027/10000000000000:ℝ) ≤ wfun x := by
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

theorem wc_285 (x : ℝ) (h₁ : (11/4:ℝ) ≤ x) (h₂ : x ≤ (89/32:ℝ)) : (41549598057/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (6872233929/10000000000:ℝ) ≤ Real.pi * ((3:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((3:ℝ) - x) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((3:ℝ) - x)) ≤ (24156576739/31250000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (6872233929/10000000000:ℝ) + taylorErr ≤ (24156576739/31250000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (158598320461/250000000000:ℝ) ≤ Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (158598320461/250000000000:ℝ) ≤ taylorSin (6872233929/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-24156576739/31250000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-88388347351/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (158598320461/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (176776695861/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (8639379797371/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (8737554567797/1000000000000:ℝ) := by nlinarith
  have hp1 : (1787270163603/125000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (14460640608583/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (9070657477039/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (409008682691/40000000000:ℝ) := by nlinarith
  have hN : (9777764255847/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (151689719650461/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (9777764255847/1000000000000:ℝ) (151689719650461/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (41549598057/10000000000000:ℝ) ≤ ((9777764255847/1000000000000:ℝ)/(151689719650461/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_286 (x : ℝ) (h₁ : (89/32:ℝ) ≤ x) (h₂ : x ≤ (179/64:ℝ)) : (37442452611/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (6381360077/10000000000:ℝ) ≤ Real.pi * ((3:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((3:ℝ) - x) ≤ (687223393/1000000000:ℝ) := by nlinarith
  have hc1 : (38650522553/50000000000:ℝ) ≤ Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (38650522553/50000000000:ℝ) ≤ taylorCos (687223393/1000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((3:ℝ) - x)) ≤ (803207533769/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (6381360077/10000000000:ℝ) + taylorErr ≤ (803207533769/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (595699302181/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (595699302181/1000000000000:ℝ) ≤ taylorSin (6381360077/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((3:ℝ) - x)) ≤ (317196643223/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (687223393/1000000000:ℝ) + taylorErr ≤ (317196643223/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h, cos_flip (3:ℝ) x, sin_flip (3:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h, cos_flip (3:ℝ) x, sin_flip (3:ℝ) x]; ring
  have hcxl : (-803207533769/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-38650522553/50000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (595699302181/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (317196643223/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (2184388641949/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (8786641953009/1000000000000:ℝ) := by nlinarith
  have hp1 : (14460640414607/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3635470040641/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (8614193404071/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (9225271147433/1000000000000:ℝ) := by nlinarith
  have hN : (9387203855131/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (38352538405189/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (9387203855131/1000000000000:ℝ) (38352538405189/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (37442452611/10000000000000:ℝ) ≤ ((9387203855131/1000000000000:ℝ)/(38352538405189/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_287 (x : ℝ) (h₁ : (179/64:ℝ) ≤ x) (h₂ : x ≤ (747/256:ℝ)) : (1457053011/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2577087723/10000000000:ℝ) ≤ Real.pi * ((3:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((3:ℝ) - x) ≤ (3190680039/5000000000:ℝ) := by nlinarith
  have hc1 : (160641505837/200000000000:ℝ) ≤ Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (160641505837/200000000000:ℝ) ≤ taylorCos (3190680039/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((3:ℝ) - x)) ≤ (241744118331/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2577087723/10000000000:ℝ) + taylorErr ≤ (241744118331/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (796455179/3125000000:ℝ) ≤ Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (796455179/3125000000:ℝ) ≤ taylorSin (2577087723/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((3:ℝ) - x)) ≤ (297849653393/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3190680039/5000000000:ℝ) + taylorErr ≤ (297849653393/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h, cos_flip (3:ℝ) x, sin_flip (3:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h, cos_flip (3:ℝ) x, sin_flip (3:ℝ) x]; ring
  have hcxl : (-241744118331/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-160641505837/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (796455179/3125000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (297849653393/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (549165122063/62500000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1833413837681/200000000000:ℝ) := by nlinarith
  have hp1 : (14541879967497/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3034297341183/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1853112898001/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (9037644113627/1000000000000:ℝ) := by nlinarith
  have hN : (4509433325187/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (167070315010009/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4509433325187/1000000000000:ℝ) (167070315010009/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1457053011/2000000000000:ℝ) ≤ ((4509433325187/1000000000000:ℝ)/(167070315010009/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_288 (x : ℝ) (h₁ : (23/8:ℝ) ≤ x) (h₂ : x ≤ (383/128:ℝ)) : (269743281/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/5000000000:ℝ) ≤ Real.pi * ((3:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((3:ℝ) - x) ≤ (3926990817/10000000000:ℝ) := by nlinarith
  have hc1 : (923879530249/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (923879530249/1000000000000:ℝ) ≤ taylorCos (3926990817/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((3:ℝ) - x)) ≤ (999698820959/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/5000000000:ℝ) + taylorErr ≤ (999698820959/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (4908245251/200000000000:ℝ) ≤ Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (4908245251/200000000000:ℝ) ≤ taylorSin (122718463/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-999698820959/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-923879530249/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (4908245251/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (95670858657/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (903207887907/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2350058567041/250000000000:ℝ) := by nlinarith
  have hp1 : (14948077731953/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (622294983493/40000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (366844157697/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (744193692609/125000000000:ℝ) := by nlinarith
  have hN : (645361843973/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (17572880859273/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (645361843973/500000000000:ℝ) (17572880859273/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (269743281/5000000000000:ℝ) ≤ ((645361843973/500000000000:ℝ)/(17572880859273/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_289 (x : ℝ) (h₁ : (373/128:ℝ) ≤ x) (h₂ : x ≤ (383/128:ℝ)) : (288828359/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/5000000000:ℝ) ≤ Real.pi * ((3:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((3:ℝ) - x) ≤ (2699806187/10000000000:ℝ) := by nlinarith
  have hc1 : (38551042541/40000000000:ℝ) ≤ Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (38551042541/40000000000:ℝ) ≤ taylorCos (2699806187/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((3:ℝ) - x)) ≤ (999698820959/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/5000000000:ℝ) + taylorErr ≤ (999698820959/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (4908245251/200000000000:ℝ) ≤ Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (4908245251/200000000000:ℝ) ≤ taylorSin (122718463/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((3:ℝ) - x)) ≤ (33339094971/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2699806187/10000000000:ℝ) + taylorErr ≤ (33339094971/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h, cos_flip (3:ℝ) x, sin_flip (3:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h, cos_flip (3:ℝ) x, sin_flip (3:ℝ) x]; ring
  have hcxl : (-999698820959/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-38551042541/40000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (4908245251/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (33339094971/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9154797342101/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2350058567041/250000000000:ℝ) := by nlinarith
  have hp1 : (15151176614181/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (622294983493/40000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (185914226659/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (4149350310931/1000000000000:ℝ) := by nlinarith
  have hN : (1335604516843/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (17572880859273/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1335604516843/1000000000000:ℝ) (17572880859273/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (288828359/5000000000000:ℝ) ≤ ((1335604516843/1000000000000:ℝ)/(17572880859273/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_290 (x : ℝ) (h₁ : (747/256:ℝ) ≤ x) (h₂ : x ≤ (6007/2048:ℝ)) : (2995265257/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2101553679/10000000000:ℝ) ≤ Real.pi * ((3:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((3:ℝ) - x) ≤ (644271931/2500000000:ℝ) := by nlinarith
  have hc1 : (483488234387/500000000000:ℝ) ≤ Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (483488234387/500000000000:ℝ) ≤ taylorCos (644271931/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((3:ℝ) - x)) ≤ (195599703441/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2101553679/10000000000:ℝ) + taylorErr ≤ (195599703441/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (208611849677/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (208611849677/1000000000000:ℝ) ≤ taylorSin (2101553679/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((3:ℝ) - x)) ≤ (254865661901/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (644271931/2500000000:ℝ) + taylorErr ≤ (254865661901/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h, cos_flip (3:ℝ) x, sin_flip (3:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h, cos_flip (3:ℝ) x, sin_flip (3:ℝ) x]; ring
  have hcxl : (-195599703441/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-483488234387/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (208611849677/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (254865661901/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (2291767297101/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (921462259283/100000000000:ℝ) := by nlinarith
  have hp1 : (3792871625601/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3050037504767/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (197809491351/62500000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (3886749137377/1000000000000:ℝ) := by nlinarith
  have hN : (413192833039/100000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (168818539056587/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (413192833039/100000000000:ℝ) (168818539056587/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2995265257/5000000000000:ℝ) ≤ ((413192833039/100000000000:ℝ)/(168818539056587/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_291 (x : ℝ) (h₁ : (747/256:ℝ) ≤ x) (h₂ : x ≤ (3019/1024:ℝ)) : (100676353/250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (325203927/2000000000:ℝ) ≤ Real.pi * ((3:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((3:ℝ) - x) ≤ (644271931/2500000000:ℝ) := by nlinarith
  have hc1 : (483488234387/500000000000:ℝ) ≤ Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (483488234387/500000000000:ℝ) ≤ taylorCos (644271931/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((3:ℝ) - x)) ≤ (986809404079/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (325203927/2000000000:ℝ) + taylorErr ≤ (986809404079/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (80943195751/500000000000:ℝ) ≤ Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (80943195751/500000000000:ℝ) ≤ taylorSin (325203927/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((3:ℝ) - x)) ≤ (254865661901/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (644271931/2500000000:ℝ) + taylorErr ≤ (254865661901/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h, cos_flip (3:ℝ) x, sin_flip (3:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h, cos_flip (3:ℝ) x, sin_flip (3:ℝ) x]; ring
  have hcxl : (-986809404079/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-483488234387/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (80943195751/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (254865661901/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (2291767297101/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (4631087998627/500000000000:ℝ) := by nlinarith
  have hp1 : (3792871625601/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15328888341753/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (491211440719/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (976701818357/250000000000:ℝ) := by nlinarith
  have hN : (3423033672369/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (170575808408217/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3423033672369/1000000000000:ℝ) (170575808408217/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (100676353/250000000000:ℝ) ≤ ((3423033672369/1000000000000:ℝ)/(170575808408217/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_292 (x : ℝ) (h₁ : (747/256:ℝ) ≤ x) (h₂ : x ≤ (1525/512:ℝ)) : (261299809/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (337475773/5000000000:ℝ) ≤ Real.pi * ((3:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((3:ℝ) - x) ≤ (644271931/2500000000:ℝ) := by nlinarith
  have hc1 : (483488234387/500000000000:ℝ) ≤ Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (483488234387/500000000000:ℝ) ≤ taylorCos (644271931/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((3:ℝ) - x)) ≤ (997723068911/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (337475773/5000000000:ℝ) + taylorErr ≤ (997723068911/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (13488783447/200000000000:ℝ) ≤ Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (13488783447/200000000000:ℝ) ≤ taylorSin (337475773/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((3:ℝ) - x)) ≤ (254865661901/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (644271931/2500000000:ℝ) + taylorErr ≤ (254865661901/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h, cos_flip (3:ℝ) x, sin_flip (3:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h, cos_flip (3:ℝ) x, sin_flip (3:ℝ) x]; ring
  have hcxl : (-997723068911/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-483488234387/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (13488783447/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (254865661901/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (2291767297101/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9357282806103/1000000000000:ℝ) := by nlinarith
  have hp1 : (3792871625601/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15486289977591/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (6395153/6250000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (394692354553/100000000000:ℝ) := by nlinarith
  have hN : (995100474387/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (87058741513391/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (995100474387/500000000000:ℝ) (87058741513391/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (261299809/2000000000000:ℝ) ≤ ((995100474387/500000000000:ℝ)/(87058741513391/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_293 (x : ℝ) (h₁ : (6007/2048:ℝ) ≤ x) (h₂ : x ≤ (12045/4096:ℝ)) : (2512351653/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1863786657/10000000000:ℝ) ≤ Real.pi * ((3:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((3:ℝ) - x) ≤ (26269421/125000000:ℝ) := by nlinarith
  have hc1 : (48899925633/50000000000:ℝ) ≤ Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (48899925633/50000000000:ℝ) ≤ taylorCos (26269421/125000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((3:ℝ) - x)) ≤ (491340859027/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1863786657/10000000000:ℝ) + taylorErr ≤ (491340859027/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (37060299303/200000000000:ℝ) ≤ Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (37060299303/200000000000:ℝ) ≤ taylorSin (1863786657/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((3:ℝ) - x)) ≤ (208611854299/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (26269421/125000000:ℝ) + taylorErr ≤ (208611854299/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h, cos_flip (3:ℝ) x, sin_flip (3:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h, cos_flip (3:ℝ) x, sin_flip (3:ℝ) x]; ring
  have hcxl : (-491340859027/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-48899925633/50000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (37060299303/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (208611854299/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9214622592829/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (4619199647521/500000000000:ℝ) := by nlinarith
  have hp1 : (3812546829817/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (7644768966397/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1412941266197/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (199348678721/62500000000:ℝ) := by nlinarith
  have hN : (1901940522527/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (84848021534633/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1901940522527/500000000000:ℝ) (84848021534633/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2512351653/5000000000000:ℝ) ≤ ((1901940522527/500000000000:ℝ)/(84848021534633/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_294 (x : ℝ) (h₁ : (6007/2048:ℝ) ≤ x) (h₂ : x ≤ (3019/1024:ℝ)) : (816631931/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (325203927/2000000000:ℝ) ≤ Real.pi * ((3:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((3:ℝ) - x) ≤ (26269421/125000000:ℝ) := by nlinarith
  have hc1 : (48899925633/50000000000:ℝ) ≤ Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (48899925633/50000000000:ℝ) ≤ taylorCos (26269421/125000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((3:ℝ) - x)) ≤ (986809404079/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (325203927/2000000000:ℝ) + taylorErr ≤ (986809404079/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (80943195751/500000000000:ℝ) ≤ Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (80943195751/500000000000:ℝ) ≤ taylorSin (325203927/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((3:ℝ) - x)) ≤ (208611854299/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (26269421/125000000:ℝ) + taylorErr ≤ (208611854299/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h, cos_flip (3:ℝ) x, sin_flip (3:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h, cos_flip (3:ℝ) x, sin_flip (3:ℝ) x]; ring
  have hcxl : (-986809404079/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-48899925633/50000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (80943195751/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (208611854299/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9214622592829/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (4631087998627/500000000000:ℝ) := by nlinarith
  have hp1 : (3812546829817/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15328888341753/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (493759558969/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (799446955329/250000000000:ℝ) := by nlinarith
  have hN : (689359261501/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (170575808408217/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (689359261501/200000000000:ℝ) (170575808408217/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (816631931/2000000000000:ℝ) ≤ ((689359261501/200000000000:ℝ)/(170575808408217/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_295 (x : ℝ) (h₁ : (12045/4096:ℝ) ≤ x) (h₂ : x ≤ (3019/1024:ℝ)) : (821878027/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (325203927/2000000000:ℝ) ≤ Real.pi * ((3:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((3:ℝ) - x) ≤ (931893329/5000000000:ℝ) := by nlinarith
  have hc1 : (982681713511/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (982681713511/1000000000000:ℝ) ≤ taylorCos (931893329/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((3:ℝ) - x)) ≤ (986809404079/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (325203927/2000000000:ℝ) + taylorErr ≤ (986809404079/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (80943195751/500000000000:ℝ) ≤ Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (80943195751/500000000000:ℝ) ≤ taylorSin (325203927/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((3:ℝ) - x)) ≤ (92650750569/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (931893329/5000000000:ℝ) + taylorErr ≤ (92650750569/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h, cos_flip (3:ℝ) x, sin_flip (3:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h, cos_flip (3:ℝ) x, sin_flip (3:ℝ) x]; ring
  have hcxl : (-986809404079/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-982681713511/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (80943195751/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (92650750569/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9238399295041/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (4631087998627/500000000000:ℝ) := by nlinarith
  have hp1 : (15289537727699/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15328888341753/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (247516809047/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (355058252563/125000000000:ℝ) := by nlinarith
  have hN : (3457849803981/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (170575808408217/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3457849803981/1000000000000:ℝ) (170575808408217/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (821878027/2000000000000:ℝ) ≤ ((3457849803981/1000000000000:ℝ)/(170575808408217/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_296 (x : ℝ) (h₁ : (3019/1024:ℝ) ≤ x) (h₂ : x ≤ (24183/8192:ℝ)) : (3697248069/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (376784031/2500000000:ℝ) ≤ Real.pi * ((3:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((3:ℝ) - x) ≤ (406504909/2500000000:ℝ) := by nlinarith
  have hc1 : (493404699769/500000000000:ℝ) ≤ Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (493404699769/500000000000:ℝ) ≤ taylorCos (406504909/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((3:ℝ) - x)) ≤ (988664187541/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (376784031/2500000000:ℝ) + taylorErr ≤ (988664187541/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (150143691403/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (150143691403/1000000000000:ℝ) ≤ taylorSin (376784031/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((3:ℝ) - x)) ≤ (1295091169/8000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (406504909/2500000000:ℝ) + taylorErr ≤ (1295091169/8000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h, cos_flip (3:ℝ) x, sin_flip (3:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h, cos_flip (3:ℝ) x, sin_flip (3:ℝ) x]; ring
  have hcxl : (-988664187541/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-493404699769/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (150143691403/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1295091169/8000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9262175997253/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (231851608709/25000000000:ℝ) := by nlinarith
  have hp1 : (1532888813613/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15348563546233/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1150767924931/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (621180909549/250000000000:ℝ) := by nlinarith
  have hN : (16441726247/5000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (42754134768761/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (16441726247/5000000000:ℝ) (42754134768761/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (3697248069/10000000000000:ℝ) ≤ ((16441726247/5000000000:ℝ)/(42754134768761/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_297 (x : ℝ) (h₁ : (3019/1024:ℝ) ≤ x) (h₂ : x ≤ (12107/4096:ℝ)) : (3285883949/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1388252613/10000000000:ℝ) ≤ Real.pi * ((3:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((3:ℝ) - x) ≤ (406504909/2500000000:ℝ) := by nlinarith
  have hc1 : (493404699769/500000000000:ℝ) ≤ Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (493404699769/500000000000:ℝ) ≤ taylorCos (406504909/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((3:ℝ) - x)) ≤ (24759481047/25000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1388252613/10000000000:ℝ) + taylorErr ≤ (24759481047/25000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (8648735707/62500000000:ℝ) ≤ Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (8648735707/62500000000:ℝ) ≤ taylorSin (1388252613/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((3:ℝ) - x)) ≤ (1295091169/8000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (406504909/2500000000:ℝ) + taylorErr ≤ (1295091169/8000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h, cos_flip (3:ℝ) x, sin_flip (3:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h, cos_flip (3:ℝ) x, sin_flip (3:ℝ) x]; ring
  have hcxl : (-24759481047/25000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-493404699769/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (8648735707/62500000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1295091169/8000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9262175997253/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (4642976349733/500000000000:ℝ) := by nlinarith
  have hp1 : (1532888813613/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1921029843839/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (265151004343/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1243954393071/500000000000:ℝ) := by nlinarith
  have hN : (1554008717141/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (1071611469209/6250000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1554008717141/500000000000:ℝ) (1071611469209/6250000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (3285883949/10000000000000:ℝ) ≤ ((1554008717141/500000000000:ℝ)/(1071611469209/6250000000:ℝ))^2 := by norm_num
  linarith

theorem wc_298 (x : ℝ) (h₁ : (3019/1024:ℝ) ≤ x) (h₂ : x ≤ (6069/2048:ℝ)) : (2539642107/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (115048559/1000000000:ℝ) ≤ Real.pi * ((3:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((3:ℝ) - x) ≤ (406504909/2500000000:ℝ) := by nlinarith
  have hc1 : (493404699769/500000000000:ℝ) ≤ Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (493404699769/500000000000:ℝ) ≤ taylorCos (406504909/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((3:ℝ) - x)) ≤ (993389213421/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (115048559/1000000000:ℝ) + taylorErr ≤ (993389213421/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (57397462127/500000000000:ℝ) ≤ Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (57397462127/500000000000:ℝ) ≤ taylorSin (115048559/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((3:ℝ) - x)) ≤ (1295091169/8000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (406504909/2500000000:ℝ) + taylorErr ≤ (1295091169/8000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h, cos_flip (3:ℝ) x, sin_flip (3:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h, cos_flip (3:ℝ) x, sin_flip (3:ℝ) x]; ring
  have hcxl : (-993389213421/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-493404699769/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (57397462127/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1295091169/8000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9262175997253/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (4654864700839/500000000000:ℝ) := by nlinarith
  have hp1 : (1532888813613/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15407589159671/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (351935710497/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1247139541017/500000000000:ℝ) := by nlinarith
  have hN : (2746487952023/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (21542765383117/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2746487952023/1000000000000:ℝ) (21542765383117/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2539642107/10000000000000:ℝ) ≤ ((2746487952023/1000000000000:ℝ)/(21542765383117/125000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_299 (x : ℝ) (h₁ : (3019/1024:ℝ) ≤ x) (h₂ : x ≤ (1525/512:ℝ)) : (67339097/500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (337475773/5000000000:ℝ) ≤ Real.pi * ((3:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((3:ℝ) - x) ≤ (406504909/2500000000:ℝ) := by nlinarith
  have hc1 : (493404699769/500000000000:ℝ) ≤ Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (493404699769/500000000000:ℝ) ≤ taylorCos (406504909/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((3:ℝ) - x)) ≤ (997723068911/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (337475773/5000000000:ℝ) + taylorErr ≤ (997723068911/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (13488783447/200000000000:ℝ) ≤ Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (13488783447/200000000000:ℝ) ≤ taylorSin (337475773/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((3:ℝ) - x)) ≤ (1295091169/8000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (406504909/2500000000:ℝ) + taylorErr ≤ (1295091169/8000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h, cos_flip (3:ℝ) x, sin_flip (3:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h, cos_flip (3:ℝ) x, sin_flip (3:ℝ) x]; ring
  have hcxl : (-997723068911/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-493404699769/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (13488783447/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1295091169/8000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9262175997253/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9357282806103/1000000000000:ℝ) := by nlinarith
  have hp1 : (1532888813613/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15486289977591/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1033840262757/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (2507019673819/1000000000000:ℝ) := by nlinarith
  have hN : (404129932459/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (87058741513391/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (404129932459/200000000000:ℝ) (87058741513391/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (67339097/500000000000:ℝ) ≤ ((404129932459/200000000000:ℝ)/(87058741513391/500000000000:ℝ))^2 := by norm_num
  linarith

end Zeta23Ext.Bridge.FourPoint
