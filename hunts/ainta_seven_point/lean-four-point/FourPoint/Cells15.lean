import FourPoint.Base

noncomputable section
open Real
namespace Zeta23Ext.Bridge.FourPoint


theorem wc_900 (x : ℝ) (h₁ : (8329/2048:ℝ) ≤ x) (h₂ : x ≤ (8349/2048:ℝ)) : (55096489/500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2101553679/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2408349837/10000000000:ℝ) := by nlinarith
  have hc1 : (971139156187/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (971139156187/1000000000000:ℝ) ≤ taylorCos (2408349837/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (195599703441/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2101553679/10000000000:ℝ) + taylorErr ≤ (195599703441/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (208611849677/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (208611849677/1000000000000:ℝ) ≤ taylorSin (2101553679/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (195599703441/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (208611849677/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (59628399277/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12776525982299/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6403602799029/500000000000:ℝ) := by nlinarith
  have hp1 : (845805295037/40000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (4239181476161/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2205562588303/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1263878028341/250000000000:ℝ) := by nlinarith
  have hN : (3433126659401/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (327049030461857/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3433126659401/1000000000000:ℝ) (327049030461857/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (55096489/500000000000:ℝ) ≤ ((3433126659401/1000000000000:ℝ)/(327049030461857/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_901 (x : ℝ) (h₁ : (8329/2048:ℝ) ≤ x) (h₂ : x ≤ (4177/1024:ℝ)) : (549643007/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2101553679/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2485048877/10000000000:ℝ) := by nlinarith
  have hc1 : (969281233079/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (969281233079/1000000000000:ℝ) ≤ taylorCos (2485048877/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (195599703441/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2101553679/10000000000:ℝ) + taylorErr ≤ (195599703441/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (208611849677/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (208611849677/1000000000000:ℝ) ≤ taylorSin (2101553679/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (195599703441/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (208611849677/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (245955052659/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12776525982299/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12814875501997/1000000000000:ℝ) := by nlinarith
  have hp1 : (845805295037/40000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21208601061113/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2205562588303/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (521636259081/100000000000:ℝ) := by nlinarith
  have hN : (3433126659401/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (163721034131683/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3433126659401/1000000000000:ℝ) (163721034131683/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (549643007/5000000000000:ℝ) ≤ ((3433126659401/1000000000000:ℝ)/(163721034131683/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_902 (x : ℝ) (h₁ : (33321/8192:ℝ) ≤ x) (h₂ : x ≤ (4167/1024:ℝ)) : (1136390777/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2120728439/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2178252719/10000000000:ℝ) := by nlinarith
  have hc1 : (976369729063/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (976369729063/1000000000000:ℝ) ≤ taylorCos (2178252719/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (977596711321/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2120728439/10000000000:ℝ) + taylorErr ≤ (977596711321/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (42097350741/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (42097350741/200000000000:ℝ) ≤ taylorSin (2120728439/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (108053399679/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2178252719/10000000000:ℝ) + taylorErr ≤ (108053399679/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (976369729063/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (977596711321/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (42097350741/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (108053399679/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3194610864571/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12784195886239/1000000000000:ℝ) := by nlinarith
  have hp1 : (528707644899/25000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (169262610719/8000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (556429779169/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (4572350131683/1000000000000:ℝ) := by nlinarith
  have hN : (3473841522031/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (325871328915461/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3473841522031/1000000000000:ℝ) (325871328915461/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1136390777/10000000000000:ℝ) ≤ ((3473841522031/1000000000000:ℝ)/(325871328915461/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_903 (x : ℝ) (h₁ : (33321/8192:ℝ) ≤ x) (h₂ : x ≤ (33341/8192:ℝ)) : (567853581/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2120728439/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2197427479/10000000000:ℝ) := by nlinarith
  have hc1 : (195190710961/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (195190710961/200000000000:ℝ) ≤ taylorCos (2197427479/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (977596711321/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2120728439/10000000000:ℝ) + taylorErr ≤ (977596711321/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (42097350741/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (42097350741/200000000000:ℝ) ≤ taylorSin (2120728439/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (27247320807/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2197427479/10000000000:ℝ) + taylorErr ≤ (27247320807/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (195190710961/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (977596711321/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (42097350741/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (27247320807/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3194610864571/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (799132085139/62500000000:ℝ) := by nlinarith
  have hp1 : (528707644899/25000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21160999759953/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (556429779169/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (4612644392451/1000000000000:ℝ) := by nlinarith
  have hN : (3473841522031/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (325969389823287/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3473841522031/1000000000000:ℝ) (325969389823287/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (567853581/5000000000000:ℝ) ≤ ((3473841522031/1000000000000:ℝ)/(325969389823287/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_904 (x : ℝ) (h₁ : (33321/8192:ℝ) ≤ x) (h₂ : x ≤ (16673/4096:ℝ)) : (1135024061/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2120728439/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2216602239/10000000000:ℝ) := by nlinarith
  have hc1 : (195106758449/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (195106758449/200000000000:ℝ) ≤ taylorCos (2216602239/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (977596711321/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2120728439/10000000000:ℝ) + taylorErr ≤ (977596711321/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (42097350741/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (42097350741/200000000000:ℝ) ≤ taylorSin (2120728439/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (21984953211/100000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2216602239/10000000000:ℝ) + taylorErr ≤ (21984953211/100000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (195106758449/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (977596711321/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (42097350741/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (21984953211/100000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3194610864571/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12788030838209/1000000000000:ℝ) := by nlinarith
  have hp1 : (528707644899/25000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2116417318003/100000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (556429779169/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (37223468569/8000000000:ℝ) := by nlinarith
  have hN : (3473841522031/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (326067465437969/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3473841522031/1000000000000:ℝ) (326067465437969/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1135024061/10000000000000:ℝ) ≤ ((3473841522031/1000000000000:ℝ)/(326067465437969/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_905 (x : ℝ) (h₁ : (16663/4096:ℝ) ≤ x) (h₂ : x ≤ (66677/16384:ℝ)) : (1162834311/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2139903199/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2187840099/10000000000:ℝ) := by nlinarith
  have hc1 : (122020261321/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (122020261321/125000000000:ℝ) ≤ taylorCos (2187840099/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (488595655547/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2139903199/10000000000:ℝ) + taylorErr ≤ (488595655547/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (106180441917/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (106180441917/500000000000:ℝ) ≤ taylorSin (2139903199/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (108521391329/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2187840099/10000000000:ℝ) + taylorErr ≤ (108521391329/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (122020261321/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (488595655547/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (106180441917/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (108521391329/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12780360934269/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1598144328029/125000000000:ℝ) := by nlinarith
  have hp1 : (4230295843199/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (4231882609983/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (898349364141/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1148124471941/250000000000:ℝ) := by nlinarith
  have hN : (3514555509611/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (162960178765521/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3514555509611/1000000000000:ℝ) (162960178765521/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1162834311/10000000000000:ℝ) ≤ ((3514555509611/1000000000000:ℝ)/(162960178765521/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_906 (x : ℝ) (h₁ : (16663/4096:ℝ) ≤ x) (h₂ : x ≤ (33341/8192:ℝ)) : (116248451/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2139903199/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2197427479/10000000000:ℝ) := by nlinarith
  have hc1 : (195190710961/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (195190710961/200000000000:ℝ) ≤ taylorCos (2197427479/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (488595655547/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2139903199/10000000000:ℝ) + taylorErr ≤ (488595655547/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (106180441917/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (106180441917/500000000000:ℝ) ≤ taylorSin (2139903199/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (27247320807/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2197427479/10000000000:ℝ) + taylorErr ≤ (27247320807/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (195190710961/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (488595655547/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (106180441917/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (27247320807/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12780360934269/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (799132085139/62500000000:ℝ) := by nlinarith
  have hp1 : (4230295843199/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21160999759953/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (898349364141/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (4612644392451/1000000000000:ℝ) := by nlinarith
  have hN : (3514555509611/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (325969389823287/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3514555509611/1000000000000:ℝ) (325969389823287/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (116248451/1000000000000:ℝ) ≤ ((3514555509611/1000000000000:ℝ)/(325969389823287/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_907 (x : ℝ) (h₁ : (16663/4096:ℝ) ≤ x) (h₂ : x ≤ (16673/4096:ℝ)) : (145223163/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2139903199/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2216602239/10000000000:ℝ) := by nlinarith
  have hc1 : (195106758449/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (195106758449/200000000000:ℝ) ≤ taylorCos (2216602239/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (488595655547/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2139903199/10000000000:ℝ) + taylorErr ≤ (488595655547/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (106180441917/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (106180441917/500000000000:ℝ) ≤ taylorSin (2139903199/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (21984953211/100000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2216602239/10000000000:ℝ) + taylorErr ≤ (21984953211/100000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (195106758449/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (488595655547/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (106180441917/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (21984953211/100000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12780360934269/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12788030838209/1000000000000:ℝ) := by nlinarith
  have hp1 : (4230295843199/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2116417318003/100000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (898349364141/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (37223468569/8000000000:ℝ) := by nlinarith
  have hN : (3514555509611/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (326067465437969/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3514555509611/1000000000000:ℝ) (326067465437969/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (145223163/1250000000000:ℝ) ≤ ((3514555509611/1000000000000:ℝ)/(326067465437969/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_908 (x : ℝ) (h₁ : (16663/4096:ℝ) ≤ x) (h₂ : x ≤ (33351/8192:ℝ)) : (36283957/312500000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2139903199/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2235776999/10000000000:ℝ) := by nlinarith
  have hc1 : (975110442927/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (975110442927/1000000000000:ℝ) ≤ taylorCos (2235776999/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (488595655547/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2139903199/10000000000:ℝ) + taylorErr ≤ (488595655547/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (106180441917/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (106180441917/500000000000:ℝ) ≤ taylorSin (2139903199/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (1385748059/6250000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2235776999/10000000000:ℝ) + taylorErr ≤ (1385748059/6250000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (975110442927/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (488595655547/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (106180441917/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1385748059/6250000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12780360934269/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6394974157097/500000000000:ℝ) := by nlinarith
  have hp1 : (4230295843199/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5291836650027/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (898349364141/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (938643502889/200000000000:ℝ) := by nlinarith
  have hN : (3514555509611/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (81541388939877/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3514555509611/1000000000000:ℝ) (81541388939877/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (36283957/312500000000:ℝ) ≤ ((3514555509611/1000000000000:ℝ)/(81541388939877/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_909 (x : ℝ) (h₁ : (16663/4096:ℝ) ≤ x) (h₂ : x ≤ (8339/2048:ℝ)) : (290097117/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2139903199/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2254951759/10000000000:ℝ) := by nlinarith
  have hc1 : (121835438551/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (121835438551/125000000000:ℝ) ≤ taylorCos (2254951759/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (488595655547/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2139903199/10000000000:ℝ) + taylorErr ≤ (488595655547/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (106180441917/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (106180441917/500000000000:ℝ) ≤ taylorSin (2139903199/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (223589031571/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2254951759/10000000000:ℝ) + taylorErr ≤ (223589031571/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (121835438551/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (488595655547/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (106180441917/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (223589031571/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12780360934269/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12791865790179/1000000000000:ℝ) := by nlinarith
  have hp1 : (4230295843199/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (4234104004037/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (898349364141/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (295843504323/62500000000:ℝ) := by nlinarith
  have hN : (3514555509611/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (5097869699811/15625000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3514555509611/1000000000000:ℝ) (5097869699811/15625000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (290097117/2500000000000:ℝ) ≤ ((3514555509611/1000000000000:ℝ)/(5097869699811/15625000000:ℝ))^2 := by norm_num
  linarith

theorem wc_910 (x : ℝ) (h₁ : (16663/4096:ℝ) ≤ x) (h₂ : x ≤ (16683/4096:ℝ)) : (1158993733/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2139903199/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1146650639/5000000000:ℝ) := by nlinarith
  have hc1 : (973818890081/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (973818890081/1000000000000:ℝ) ≤ taylorCos (1146650639/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (488595655547/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2139903199/10000000000:ℝ) + taylorErr ≤ (488595655547/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (106180441917/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (106180441917/500000000000:ℝ) ≤ taylorSin (2139903199/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (488595655547/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (106180441917/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (113662621323/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12780360934269/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12795700742149/1000000000000:ℝ) := by nlinarith
  have hp1 : (4230295843199/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21176866860341/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (898349364141/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (481403639751/100000000000:ℝ) := by nlinarith
  have hN : (3514555509611/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (65291982993053/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3514555509611/1000000000000:ℝ) (65291982993053/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1158993733/10000000000000:ℝ) ≤ ((3514555509611/1000000000000:ℝ)/(65291982993053/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_911 (x : ℝ) (h₁ : (16663/4096:ℝ) ≤ x) (h₂ : x ≤ (1043/256:ℝ)) : (1157601093/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2139903199/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1165825399/5000000000:ℝ) := by nlinarith
  have hc1 : (486469974967/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (486469974967/500000000000:ℝ) ≤ taylorCos (1165825399/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (488595655547/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2139903199/10000000000:ℝ) + taylorErr ≤ (488595655547/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (106180441917/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (106180441917/500000000000:ℝ) ≤ taylorSin (2139903199/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (488595655547/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (106180441917/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (231058110583/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12780360934269/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6399767847059/500000000000:ℝ) := by nlinarith
  have hp1 : (4230295843199/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10591606850247/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (898349364141/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (4894553333713/1000000000000:ℝ) := by nlinarith
  have hN : (3514555509611/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (163328113985001/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3514555509611/1000000000000:ℝ) (163328113985001/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1157601093/10000000000000:ℝ) ≤ ((3514555509611/1000000000000:ℝ)/(163328113985001/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_912 (x : ℝ) (h₁ : (66657/16384:ℝ) ≤ x) (h₂ : x ≤ (33341/8192:ℝ)) : (1175989937/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2149490579/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2197427479/10000000000:ℝ) := by nlinarith
  have hc1 : (195190710961/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (195190710961/200000000000:ℝ) ≤ taylorCos (2197427479/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (976987263567/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2149490579/10000000000:ℝ) + taylorErr ≤ (976987263567/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (213297656533/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (213297656533/1000000000000:ℝ) ≤ taylorSin (2149490579/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (27247320807/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2197427479/10000000000:ℝ) + taylorErr ≤ (27247320807/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (195190710961/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (976987263567/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (213297656533/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (27247320807/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12781319672261/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (799132085139/62500000000:ℝ) := by nlinarith
  have hp1 : (21153065926011/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21160999759953/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2255949695253/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (4612644392451/1000000000000:ℝ) := by nlinarith
  have hN : (3534912126939/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (325969389823287/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3534912126939/1000000000000:ℝ) (325969389823287/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1175989937/10000000000000:ℝ) ≤ ((3534912126939/1000000000000:ℝ)/(325969389823287/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_913 (x : ℝ) (h₁ : (33331/8192:ℝ) ≤ x) (h₂ : x ≤ (66687/16384:ℝ)) : (594607679/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1079538979/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2207014859/10000000000:ℝ) := by nlinarith
  have hc1 : (487872060983/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (487872060983/500000000000:ℝ) ≤ taylorCos (2207014859/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (244195579509/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1079538979/5000000000:ℝ) + taylorErr ≤ (244195579509/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (8569369323/40000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (8569369323/40000000000:ℝ) ≤ taylorSin (1079538979/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (109457074947/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2207014859/10000000000:ℝ) + taylorErr ≤ (109457074947/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (487872060983/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (244195579509/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (8569369323/40000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (109457074947/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6391139205127/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12787072100217/1000000000000:ℝ) := by nlinarith
  have hp1 : (2115465263603/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2645323308749/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4532050783447/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (4632789626637/1000000000000:ℝ) := by nlinarith
  have hN : (3555268465411/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (40752303224037/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3555268465411/1000000000000:ℝ) (40752303224037/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (594607679/5000000000000:ℝ) ≤ ((3555268465411/1000000000000:ℝ)/(40752303224037/125000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_914 (x : ℝ) (h₁ : (33331/8192:ℝ) ≤ x) (h₂ : x ≤ (16673/4096:ℝ)) : (47554307/400000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1079538979/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2216602239/10000000000:ℝ) := by nlinarith
  have hc1 : (195106758449/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (195106758449/200000000000:ℝ) ≤ taylorCos (2216602239/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (244195579509/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1079538979/5000000000:ℝ) + taylorErr ≤ (244195579509/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (8569369323/40000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (8569369323/40000000000:ℝ) ≤ taylorSin (1079538979/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (21984953211/100000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2216602239/10000000000:ℝ) + taylorErr ≤ (21984953211/100000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (195106758449/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (244195579509/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (8569369323/40000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (21984953211/100000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6391139205127/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12788030838209/1000000000000:ℝ) := by nlinarith
  have hp1 : (2115465263603/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2116417318003/100000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4532050783447/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (37223468569/8000000000:ℝ) := by nlinarith
  have hN : (3555268465411/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (326067465437969/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3555268465411/1000000000000:ℝ) (326067465437969/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (47554307/400000000000:ℝ) ≤ ((3555268465411/1000000000000:ℝ)/(326067465437969/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_915 (x : ℝ) (h₁ : (33331/8192:ℝ) ≤ x) (h₂ : x ≤ (33351/8192:ℝ)) : (594071357/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1079538979/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2235776999/10000000000:ℝ) := by nlinarith
  have hc1 : (975110442927/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (975110442927/1000000000000:ℝ) ≤ taylorCos (2235776999/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (244195579509/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1079538979/5000000000:ℝ) + taylorErr ≤ (244195579509/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (8569369323/40000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (8569369323/40000000000:ℝ) ≤ taylorSin (1079538979/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (1385748059/6250000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2235776999/10000000000:ℝ) + taylorErr ≤ (1385748059/6250000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (975110442927/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (244195579509/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (8569369323/40000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1385748059/6250000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6391139205127/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6394974157097/500000000000:ℝ) := by nlinarith
  have hp1 : (2115465263603/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5291836650027/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4532050783447/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (938643502889/200000000000:ℝ) := by nlinarith
  have hN : (3555268465411/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (81541388939877/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3555268465411/1000000000000:ℝ) (81541388939877/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (594071357/5000000000000:ℝ) ≤ ((3555268465411/1000000000000:ℝ)/(81541388939877/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_916 (x : ℝ) (h₁ : (33331/8192:ℝ) ≤ x) (h₂ : x ≤ (8339/2048:ℝ)) : (118742829/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1079538979/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2254951759/10000000000:ℝ) := by nlinarith
  have hc1 : (121835438551/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (121835438551/125000000000:ℝ) ≤ taylorCos (2254951759/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (244195579509/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1079538979/5000000000:ℝ) + taylorErr ≤ (244195579509/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (8569369323/40000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (8569369323/40000000000:ℝ) ≤ taylorSin (1079538979/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (223589031571/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2254951759/10000000000:ℝ) + taylorErr ≤ (223589031571/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (121835438551/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (244195579509/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (8569369323/40000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (223589031571/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6391139205127/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12791865790179/1000000000000:ℝ) := by nlinarith
  have hp1 : (2115465263603/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (4234104004037/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4532050783447/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (295843504323/62500000000:ℝ) := by nlinarith
  have hN : (3555268465411/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (5097869699811/15625000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3555268465411/1000000000000:ℝ) (5097869699811/15625000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (118742829/1000000000000:ℝ) ≤ ((3555268465411/1000000000000:ℝ)/(5097869699811/15625000000:ℝ))^2 := by norm_num
  linarith

theorem wc_917 (x : ℝ) (h₁ : (66667/16384:ℝ) ≤ x) (h₂ : x ≤ (16673/4096:ℝ)) : (37578453/312500000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1084332669/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2216602239/10000000000:ℝ) := by nlinarith
  have hc1 : (195106758449/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (195106758449/200000000000:ℝ) ≤ taylorCos (2216602239/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (976576474647/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1084332669/5000000000:ℝ) + taylorErr ≤ (976576474647/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (53792653199/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (53792653199/250000000000:ℝ) ≤ taylorSin (1084332669/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (21984953211/100000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2216602239/10000000000:ℝ) + taylorErr ≤ (21984953211/100000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (195106758449/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (976576474647/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (53792653199/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (21984953211/100000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6391618574123/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12788030838209/1000000000000:ℝ) := by nlinarith
  have hp1 : (10578119673023/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2116417318003/100000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4552200984547/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (37223468569/8000000000:ℝ) := by nlinarith
  have hN : (35756245099/10000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (326067465437969/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (35756245099/10000000000:ℝ) (326067465437969/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (37578453/312500000000:ℝ) ≤ ((35756245099/10000000000:ℝ)/(326067465437969/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_918 (x : ℝ) (h₁ : (4167/1024:ℝ) ≤ x) (h₂ : x ≤ (16673/4096:ℝ)) : (24324821/200000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1089126359/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2216602239/10000000000:ℝ) := by nlinarith
  have hc1 : (195106758449/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (195106758449/200000000000:ℝ) ≤ taylorCos (2216602239/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (976369733609/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1089126359/5000000000:ℝ) + taylorErr ≤ (976369733609/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (13506674671/62500000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (13506674671/62500000000:ℝ) ≤ taylorSin (1089126359/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (21984953211/100000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2216602239/10000000000:ℝ) + taylorErr ≤ (21984953211/100000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (195106758449/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (976369733609/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (13506674671/62500000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (21984953211/100000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6392097943119/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12788030838209/1000000000000:ℝ) := by nlinarith
  have hp1 : (21157826056063/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2116417318003/100000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4572349972557/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (37223468569/8000000000:ℝ) := by nlinarith
  have hN : (898995059737/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (326067465437969/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (898995059737/250000000000:ℝ) (326067465437969/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (24324821/200000000000:ℝ) ≤ ((898995059737/250000000000:ℝ)/(326067465437969/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_919 (x : ℝ) (h₁ : (4167/1024:ℝ) ≤ x) (h₂ : x ≤ (66697/16384:ℝ)) : (1215875267/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1089126359/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2226189619/10000000000:ℝ) := by nlinarith
  have hc1 : (487661282917/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (487661282917/500000000000:ℝ) ≤ taylorCos (2226189619/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (976369733609/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1089126359/5000000000:ℝ) + taylorErr ≤ (976369733609/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (13506674671/62500000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (13506674671/62500000000:ℝ) ≤ taylorSin (1089126359/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (110392356123/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2226189619/10000000000:ℝ) + taylorErr ≤ (110392356123/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (487661282917/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (976369733609/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (13506674671/62500000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (110392356123/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6392097943119/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6394494788101/500000000000:ℝ) := by nlinarith
  have hp1 : (21157826056063/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2116575989007/100000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4572349972557/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (2336538103399/500000000000:ℝ) := by nlinarith
  have hN : (898995059737/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (326116508760407/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (898995059737/250000000000:ℝ) (326116508760407/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1215875267/10000000000000:ℝ) ≤ ((898995059737/250000000000:ℝ)/(326116508760407/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_920 (x : ℝ) (h₁ : (4167/1024:ℝ) ≤ x) (h₂ : x ≤ (33351/8192:ℝ)) : (1215509621/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1089126359/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2235776999/10000000000:ℝ) := by nlinarith
  have hc1 : (975110442927/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (975110442927/1000000000000:ℝ) ≤ taylorCos (2235776999/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (976369733609/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1089126359/5000000000:ℝ) + taylorErr ≤ (976369733609/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (13506674671/62500000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (13506674671/62500000000:ℝ) ≤ taylorSin (1089126359/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (1385748059/6250000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2235776999/10000000000:ℝ) + taylorErr ≤ (1385748059/6250000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (975110442927/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (976369733609/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (13506674671/62500000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1385748059/6250000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6392097943119/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6394974157097/500000000000:ℝ) := by nlinarith
  have hp1 : (21157826056063/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5291836650027/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4572349972557/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (938643502889/200000000000:ℝ) := by nlinarith
  have hN : (898995059737/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (81541388939877/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (898995059737/250000000000:ℝ) (81541388939877/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1215509621/10000000000000:ℝ) ≤ ((898995059737/250000000000:ℝ)/(81541388939877/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_921 (x : ℝ) (h₁ : (4167/1024:ℝ) ≤ x) (h₂ : x ≤ (8339/2048:ℝ)) : (1214778741/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1089126359/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2254951759/10000000000:ℝ) := by nlinarith
  have hc1 : (121835438551/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (121835438551/125000000000:ℝ) ≤ taylorCos (2254951759/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (976369733609/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1089126359/5000000000:ℝ) + taylorErr ≤ (976369733609/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (13506674671/62500000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (13506674671/62500000000:ℝ) ≤ taylorSin (1089126359/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (223589031571/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2254951759/10000000000:ℝ) + taylorErr ≤ (223589031571/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (121835438551/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (976369733609/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (13506674671/62500000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (223589031571/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6392097943119/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12791865790179/1000000000000:ℝ) := by nlinarith
  have hp1 : (21157826056063/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (4234104004037/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4572349972557/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (295843504323/62500000000:ℝ) := by nlinarith
  have hN : (898995059737/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (5097869699811/15625000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (898995059737/250000000000:ℝ) (5097869699811/15625000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1214778741/10000000000000:ℝ) ≤ ((898995059737/250000000000:ℝ)/(5097869699811/15625000000:ℝ))^2 := by norm_num
  linarith

theorem wc_922 (x : ℝ) (h₁ : (4167/1024:ℝ) ≤ x) (h₂ : x ≤ (33361/8192:ℝ)) : (303512103/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1089126359/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2274126519/10000000000:ℝ) := by nlinarith
  have hc1 : (487126495129/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (487126495129/500000000000:ℝ) ≤ taylorCos (2274126519/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (976369733609/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1089126359/5000000000:ℝ) + taylorErr ≤ (976369733609/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (13506674671/62500000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (13506674671/62500000000:ℝ) ≤ taylorSin (1089126359/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (56364387907/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2274126519/10000000000:ℝ) + taylorErr ≤ (56364387907/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (487126495129/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (976369733609/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (13506674671/62500000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (56364387907/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6392097943119/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3198445816541/250000000000:ℝ) := by nlinarith
  have hp1 : (21157826056063/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21173693440263/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4572349972557/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1193442270491/250000000000:ℝ) := by nlinarith
  have hN : (898995059737/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (81590445130789/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (898995059737/250000000000:ℝ) (81590445130789/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (303512103/2500000000000:ℝ) ≤ ((898995059737/250000000000:ℝ)/(81590445130789/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_923 (x : ℝ) (h₁ : (4167/1024:ℝ) ≤ x) (h₂ : x ≤ (16683/4096:ℝ)) : (1213318631/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1089126359/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1146650639/5000000000:ℝ) := by nlinarith
  have hc1 : (973818890081/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (973818890081/1000000000000:ℝ) ≤ taylorCos (1146650639/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (976369733609/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1089126359/5000000000:ℝ) + taylorErr ≤ (976369733609/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (13506674671/62500000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (13506674671/62500000000:ℝ) ≤ taylorSin (1089126359/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (976369733609/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (13506674671/62500000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (113662621323/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6392097943119/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12795700742149/1000000000000:ℝ) := by nlinarith
  have hp1 : (21157826056063/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21176866860341/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4572349972557/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (481403639751/100000000000:ℝ) := by nlinarith
  have hN : (898995059737/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (65291982993053/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (898995059737/250000000000:ℝ) (65291982993053/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1213318631/10000000000000:ℝ) ≤ ((898995059737/250000000000:ℝ)/(65291982993053/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_924 (x : ℝ) (h₁ : (4167/1024:ℝ) ≤ x) (h₂ : x ≤ (1043/256:ℝ)) : (242372143/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1089126359/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1165825399/5000000000:ℝ) := by nlinarith
  have hc1 : (486469974967/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (486469974967/500000000000:ℝ) ≤ taylorCos (1165825399/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (976369733609/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1089126359/5000000000:ℝ) + taylorErr ≤ (976369733609/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (13506674671/62500000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (13506674671/62500000000:ℝ) ≤ taylorSin (1089126359/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (976369733609/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (13506674671/62500000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (231058110583/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6392097943119/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6399767847059/500000000000:ℝ) := by nlinarith
  have hp1 : (21157826056063/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10591606850247/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4572349972557/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (4894553333713/1000000000000:ℝ) := by nlinarith
  have hN : (898995059737/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (163328113985001/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (898995059737/250000000000:ℝ) (163328113985001/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (242372143/2000000000000:ℝ) ≤ ((898995059737/250000000000:ℝ)/(163328113985001/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_925 (x : ℝ) (h₁ : (4167/1024:ℝ) ≤ x) (h₂ : x ≤ (16693/4096:ℝ)) : (121040499/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1089126359/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1185000159/5000000000:ℝ) := by nlinarith
  have hc1 : (243011675229/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (243011675229/250000000000:ℝ) ≤ taylorCos (1185000159/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (976369733609/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1089126359/5000000000:ℝ) + taylorErr ≤ (976369733609/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (13506674671/62500000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (13506674671/62500000000:ℝ) ≤ taylorSin (1089126359/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (976369733609/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (13506674671/62500000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (117393790193/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6392097943119/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1600421330761/125000000000:ℝ) := by nlinarith
  have hp1 : (21157826056063/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21189560540649/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4572349972557/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (2487522824391/500000000000:ℝ) := by nlinarith
  have hN : (898995059737/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (40856574975277/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (898995059737/250000000000:ℝ) (40856574975277/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (121040499/1000000000000:ℝ) ≤ ((898995059737/250000000000:ℝ)/(40856574975277/125000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_926 (x : ℝ) (h₁ : (4167/1024:ℝ) ≤ x) (h₂ : x ≤ (8349/2048:ℝ)) : (1208951451/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1089126359/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2408349837/10000000000:ℝ) := by nlinarith
  have hc1 : (971139156187/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (971139156187/1000000000000:ℝ) ≤ taylorCos (2408349837/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (976369733609/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1089126359/5000000000:ℝ) + taylorErr ≤ (976369733609/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (13506674671/62500000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (13506674671/62500000000:ℝ) ≤ taylorSin (1089126359/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (976369733609/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (13506674671/62500000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (59628399277/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6392097943119/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6403602799029/500000000000:ℝ) := by nlinarith
  have hp1 : (21157826056063/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (4239181476161/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4572349972557/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1263878028341/250000000000:ℝ) := by nlinarith
  have hN : (898995059737/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (327049030461857/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (898995059737/250000000000:ℝ) (327049030461857/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1208951451/10000000000000:ℝ) ≤ ((898995059737/250000000000:ℝ)/(327049030461857/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_927 (x : ℝ) (h₁ : (4167/1024:ℝ) ≤ x) (h₂ : x ≤ (4177/1024:ℝ)) : (1206050917/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1089126359/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2485048877/10000000000:ℝ) := by nlinarith
  have hc1 : (969281233079/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (969281233079/1000000000000:ℝ) ≤ taylorCos (2485048877/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (976369733609/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1089126359/5000000000:ℝ) + taylorErr ≤ (976369733609/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (13506674671/62500000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (13506674671/62500000000:ℝ) ≤ taylorSin (1089126359/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (976369733609/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (13506674671/62500000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (245955052659/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6392097943119/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12814875501997/1000000000000:ℝ) := by nlinarith
  have hp1 : (21157826056063/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21208601061113/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4572349972557/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (521636259081/100000000000:ℝ) := by nlinarith
  have hN : (898995059737/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (163721034131683/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (898995059737/250000000000:ℝ) (163721034131683/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1206050917/10000000000000:ℝ) ≤ ((898995059737/250000000000:ℝ)/(163721034131683/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_928 (x : ℝ) (h₁ : (4167/1024:ℝ) ≤ x) (h₂ : x ≤ (8359/2048:ℝ)) : (1203159081/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1089126359/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (640436979/2500000000:ℝ) := by nlinarith
  have hc1 : (483683144977/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (483683144977/500000000000:ℝ) ≤ taylorCos (640436979/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (976369733609/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1089126359/5000000000:ℝ) + taylorErr ≤ (976369733609/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (13506674671/62500000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (13506674671/62500000000:ℝ) ≤ taylorSin (1089126359/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (976369733609/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (13506674671/62500000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (3167275491/12500000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6392097943119/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12822545405937/1000000000000:ℝ) := by nlinarith
  have hp1 : (21157826056063/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1326330921339/62500000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4572349972557/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (336068433609/62500000000:ℝ) := by nlinarith
  have hN : (898995059737/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (327835341374633/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (898995059737/250000000000:ℝ) (327835341374633/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1203159081/10000000000000:ℝ) ≤ ((898995059737/250000000000:ℝ)/(327835341374633/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_929 (x : ℝ) (h₁ : (4167/1024:ℝ) ≤ x) (h₂ : x ≤ (2091/512:ℝ)) : (600137957/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1089126359/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (659611739/2500000000:ℝ) := by nlinarith
  have hc1 : (482697219707/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (482697219707/500000000000:ℝ) ≤ taylorCos (659611739/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (976369733609/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1089126359/5000000000:ℝ) + taylorErr ≤ (976369733609/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (13506674671/62500000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (13506674671/62500000000:ℝ) ≤ taylorSin (1089126359/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (976369733609/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (13506674671/62500000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (130397060129/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6392097943119/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3207553827469/250000000000:ℝ) := by nlinarith
  have hp1 : (21157826056063/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21233988421733/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4572349972557/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1107539866003/200000000000:ℝ) := by nlinarith
  have hN : (898995059737/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (164114424897777/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (898995059737/250000000000:ℝ) (164114424897777/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (600137957/5000000000000:ℝ) ≤ ((898995059737/250000000000:ℝ)/(164114424897777/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_930 (x : ℝ) (h₁ : (4167/1024:ℝ) ≤ x) (h₂ : x ≤ (4187/1024:ℝ)) : (37329233/312500000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1089126359/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1395922517/5000000000:ℝ) := by nlinarith
  have hc1 : (240320120887/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (240320120887/250000000000:ℝ) ≤ taylorCos (1395922517/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (976369733609/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1089126359/5000000000:ℝ) + taylorErr ≤ (976369733609/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (13506674671/62500000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (13506674671/62500000000:ℝ) ≤ taylorSin (1089126359/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (976369733609/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (13506674671/62500000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (137785910789/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6392097943119/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2569111023551/200000000000:ℝ) := by nlinarith
  have hp1 : (21157826056063/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1328710986397/62500000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4572349972557/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (2929242454977/500000000000:ℝ) := by nlinarith
  have hN : (898995059737/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (82254143141641/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (898995059737/250000000000:ℝ) (82254143141641/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (37329233/312500000000:ℝ) ≤ ((898995059737/250000000000:ℝ)/(82254143141641/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_931 (x : ℝ) (h₁ : (4167/1024:ℝ) ≤ x) (h₂ : x ≤ (131/32:ℝ)) : (74301831/625000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1089126359/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2945243113/10000000000:ℝ) := by nlinarith
  have hc1 : (956940333463/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (956940333463/1000000000000:ℝ) ≤ taylorCos (2945243113/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (976369733609/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1089126359/5000000000:ℝ) + taylorErr ≤ (976369733609/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (13506674671/62500000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (13506674671/62500000000:ℝ) ≤ taylorSin (1089126359/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (976369733609/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (13506674671/62500000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (290284679541/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6392097943119/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6430447462817/500000000000:ℝ) := by nlinarith
  have hp1 : (21157826056063/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21284763142971/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4572349972557/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (48270630063/7812500000:ℝ) := by nlinarith
  have hN : (898995059737/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (329805236576397/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (898995059737/250000000000:ℝ) (329805236576397/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (74301831/625000000000:ℝ) ≤ ((898995059737/250000000000:ℝ)/(329805236576397/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_932 (x : ℝ) (h₁ : (66677/16384:ℝ) ≤ x) (h₂ : x ≤ (66697/16384:ℝ)) : (245935877/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1093920049/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2226189619/10000000000:ℝ) := by nlinarith
  have hc1 : (487661282917/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (487661282917/500000000000:ℝ) ≤ taylorCos (2226189619/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (488081047557/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1093920049/5000000000:ℝ) + taylorErr ≤ (488081047557/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (54260694509/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (54260694509/250000000000:ℝ) ≤ taylorSin (1093920049/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (110392356123/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2226189619/10000000000:ℝ) + taylorErr ≤ (110392356123/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (487661282917/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (488081047557/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (54260694509/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (110392356123/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12785154624231/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6394494788101/500000000000:ℝ) := by nlinarith
  have hp1 : (21159412766081/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2116575989007/100000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (114812443209/25000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (2336538103399/500000000000:ℝ) := by nlinarith
  have hN : (1808167816623/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (326116508760407/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1808167816623/500000000000:ℝ) (326116508760407/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (245935877/2000000000000:ℝ) ≤ ((1808167816623/500000000000:ℝ)/(326116508760407/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_933 (x : ℝ) (h₁ : (66677/16384:ℝ) ≤ x) (h₂ : x ≤ (33351/8192:ℝ)) : (307327397/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1093920049/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2235776999/10000000000:ℝ) := by nlinarith
  have hc1 : (975110442927/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (975110442927/1000000000000:ℝ) ≤ taylorCos (2235776999/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (488081047557/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1093920049/5000000000:ℝ) + taylorErr ≤ (488081047557/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (54260694509/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (54260694509/250000000000:ℝ) ≤ taylorSin (1093920049/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (1385748059/6250000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2235776999/10000000000:ℝ) + taylorErr ≤ (1385748059/6250000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (975110442927/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (488081047557/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (54260694509/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1385748059/6250000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12785154624231/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6394974157097/500000000000:ℝ) := by nlinarith
  have hp1 : (21159412766081/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5291836650027/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (114812443209/25000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (938643502889/200000000000:ℝ) := by nlinarith
  have hN : (1808167816623/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (81541388939877/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1808167816623/500000000000:ℝ) (81541388939877/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (307327397/2500000000000:ℝ) ≤ ((1808167816623/500000000000:ℝ)/(81541388939877/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_934 (x : ℝ) (h₁ : (33341/8192:ℝ) ≤ x) (h₂ : x ≤ (33351/8192:ℝ)) : (1243187209/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1098713739/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2235776999/10000000000:ℝ) := by nlinarith
  have hc1 : (975110442927/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (975110442927/1000000000000:ℝ) ≤ taylorCos (2235776999/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (975953559351/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1098713739/5000000000:ℝ) + taylorErr ≤ (975953559351/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (43595712367/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (43595712367/200000000000:ℝ) ≤ taylorSin (1098713739/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (1385748059/6250000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2235776999/10000000000:ℝ) + taylorErr ≤ (1385748059/6250000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (975110442927/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (975953559351/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (43595712367/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1385748059/6250000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12786113362223/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6394974157097/500000000000:ℝ) := by nlinarith
  have hp1 : (10580499738049/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5291836650027/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4612644232791/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (938643502889/200000000000:ℝ) := by nlinarith
  have hN : (22729316709/6250000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (81541388939877/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (22729316709/6250000000:ℝ) (81541388939877/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1243187209/10000000000000:ℝ) ≤ ((22729316709/6250000000:ℝ)/(81541388939877/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_935 (x : ℝ) (h₁ : (33341/8192:ℝ) ≤ x) (h₂ : x ≤ (66707/16384:ℝ)) : (621406689/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1098713739/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2245364379/10000000000:ℝ) := by nlinarith
  have hc1 : (24372435593/25000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (24372435593/25000000000:ℝ) ≤ taylorCos (2245364379/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (975953559351/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1098713739/5000000000:ℝ) + taylorErr ≤ (975953559351/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (43595712367/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (43595712367/200000000000:ℝ) ≤ taylorSin (1098713739/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (44530892567/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2245364379/10000000000:ℝ) + taylorErr ≤ (44530892567/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (24372435593/25000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (975953559351/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (43595712367/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (44530892567/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12786113362223/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6395453526093/500000000000:ℝ) := by nlinarith
  have hp1 : (10580499738049/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10584466655073/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4612644232791/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (4713357474961/1000000000000:ℝ) := by nlinarith
  have hN : (22729316709/6250000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (81553651608831/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (22729316709/6250000000:ℝ) (81553651608831/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (621406689/5000000000000:ℝ) ≤ ((22729316709/6250000000:ℝ)/(81553651608831/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_936 (x : ℝ) (h₁ : (33341/8192:ℝ) ≤ x) (h₂ : x ≤ (8339/2048:ℝ)) : (155304961/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1098713739/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2254951759/10000000000:ℝ) := by nlinarith
  have hc1 : (121835438551/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (121835438551/125000000000:ℝ) ≤ taylorCos (2254951759/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (975953559351/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1098713739/5000000000:ℝ) + taylorErr ≤ (975953559351/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (43595712367/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (43595712367/200000000000:ℝ) ≤ taylorSin (1098713739/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (223589031571/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2254951759/10000000000:ℝ) + taylorErr ≤ (223589031571/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (121835438551/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (975953559351/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (43595712367/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (223589031571/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12786113362223/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12791865790179/1000000000000:ℝ) := by nlinarith
  have hp1 : (10580499738049/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (4234104004037/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4612644232791/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (295843504323/62500000000:ℝ) := by nlinarith
  have hN : (22729316709/6250000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (5097869699811/15625000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (22729316709/6250000000:ℝ) (5097869699811/15625000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (155304961/1250000000000:ℝ) ≤ ((22729316709/6250000000:ℝ)/(5097869699811/15625000000:ℝ))^2 := by norm_num
  linarith

theorem wc_937 (x : ℝ) (h₁ : (33341/8192:ℝ) ≤ x) (h₂ : x ≤ (33361/8192:ℝ)) : (155211591/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1098713739/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2274126519/10000000000:ℝ) := by nlinarith
  have hc1 : (487126495129/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (487126495129/500000000000:ℝ) ≤ taylorCos (2274126519/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (975953559351/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1098713739/5000000000:ℝ) + taylorErr ≤ (975953559351/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (43595712367/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (43595712367/200000000000:ℝ) ≤ taylorSin (1098713739/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (56364387907/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2274126519/10000000000:ℝ) + taylorErr ≤ (56364387907/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (487126495129/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (975953559351/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (43595712367/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (56364387907/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12786113362223/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3198445816541/250000000000:ℝ) := by nlinarith
  have hp1 : (10580499738049/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21173693440263/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4612644232791/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1193442270491/250000000000:ℝ) := by nlinarith
  have hN : (22729316709/6250000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (81590445130789/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (22729316709/6250000000:ℝ) (81590445130789/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (155211591/1250000000000:ℝ) ≤ ((22729316709/6250000000:ℝ)/(81590445130789/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_938 (x : ℝ) (h₁ : (33341/8192:ℝ) ≤ x) (h₂ : x ≤ (16683/4096:ℝ)) : (124094633/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1098713739/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1146650639/5000000000:ℝ) := by nlinarith
  have hc1 : (973818890081/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (973818890081/1000000000000:ℝ) ≤ taylorCos (1146650639/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (975953559351/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1098713739/5000000000:ℝ) + taylorErr ≤ (975953559351/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (43595712367/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (43595712367/200000000000:ℝ) ≤ taylorSin (1098713739/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (975953559351/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (43595712367/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (113662621323/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12786113362223/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12795700742149/1000000000000:ℝ) := by nlinarith
  have hp1 : (10580499738049/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21176866860341/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4612644232791/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (481403639751/100000000000:ℝ) := by nlinarith
  have hN : (22729316709/6250000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (65291982993053/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (22729316709/6250000000:ℝ) (65291982993053/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (124094633/1000000000000:ℝ) ≤ ((22729316709/6250000000:ℝ)/(65291982993053/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_939 (x : ℝ) (h₁ : (66687/16384:ℝ) ≤ x) (h₂ : x ≤ (66707/16384:ℝ)) : (1256764439/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1103507429/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2245364379/10000000000:ℝ) := by nlinarith
  have hc1 : (24372435593/25000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (24372435593/25000000000:ℝ) ≤ taylorCos (2245364379/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (975744126513/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1103507429/5000000000:ℝ) + taylorErr ≤ (975744126513/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (27364268159/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (27364268159/125000000000:ℝ) ≤ taylorSin (1103507429/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (44530892567/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2245364379/10000000000:ℝ) + taylorErr ≤ (44530892567/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (24372435593/25000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (975744126513/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (27364268159/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (44530892567/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1598384012527/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6395453526093/500000000000:ℝ) := by nlinarith
  have hp1 : (5290646546529/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10584466655073/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2316394733339/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (4713357474961/1000000000000:ℝ) := by nlinarith
  have hN : (731409068033/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (81553651608831/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (731409068033/200000000000:ℝ) (81553651608831/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1256764439/10000000000000:ℝ) ≤ ((731409068033/200000000000:ℝ)/(81553651608831/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_940 (x : ℝ) (h₁ : (66687/16384:ℝ) ≤ x) (h₂ : x ≤ (8339/2048:ℝ)) : (628193277/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1103507429/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2254951759/10000000000:ℝ) := by nlinarith
  have hc1 : (121835438551/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (121835438551/125000000000:ℝ) ≤ taylorCos (2254951759/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (975744126513/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1103507429/5000000000:ℝ) + taylorErr ≤ (975744126513/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (27364268159/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (27364268159/125000000000:ℝ) ≤ taylorSin (1103507429/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (223589031571/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2254951759/10000000000:ℝ) + taylorErr ≤ (223589031571/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (121835438551/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (975744126513/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (27364268159/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (223589031571/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1598384012527/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12791865790179/1000000000000:ℝ) := by nlinarith
  have hp1 : (5290646546529/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (4234104004037/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2316394733339/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (295843504323/62500000000:ℝ) := by nlinarith
  have hN : (731409068033/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (5097869699811/15625000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (731409068033/200000000000:ℝ) (5097869699811/15625000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (628193277/5000000000000:ℝ) ≤ ((731409068033/200000000000:ℝ)/(5097869699811/15625000000:ℝ))^2 := by norm_num
  linarith

theorem wc_941 (x : ℝ) (h₁ : (16673/4096:ℝ) ≤ x) (h₂ : x ≤ (8339/2048:ℝ)) : (1270410991/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1108301119/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2254951759/10000000000:ℝ) := by nlinarith
  have hc1 : (121835438551/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (121835438551/125000000000:ℝ) ≤ taylorCos (2254951759/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (975533796791/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1108301119/5000000000:ℝ) + taylorErr ≤ (975533796791/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (3435148867/15625000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (3435148867/15625000000:ℝ) ≤ taylorSin (1108301119/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (223589031571/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2254951759/10000000000:ℝ) + taylorErr ≤ (223589031571/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (121835438551/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (975533796791/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (3435148867/15625000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (223589031571/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (199812981847/15625000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12791865790179/1000000000000:ℝ) := by nlinarith
  have hp1 : (21164172896133/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (4234104004037/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4652933410889/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (295843504323/62500000000:ℝ) := by nlinarith
  have hN : (1838699807049/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (5097869699811/15625000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1838699807049/500000000000:ℝ) (5097869699811/15625000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1270410991/10000000000000:ℝ) ≤ ((1838699807049/500000000000:ℝ)/(5097869699811/15625000000:ℝ))^2 := by norm_num
  linarith

theorem wc_942 (x : ℝ) (h₁ : (16673/4096:ℝ) ≤ x) (h₂ : x ≤ (66717/16384:ℝ)) : (158753629/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1108301119/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2264539139/10000000000:ℝ) := by nlinarith
  have hc1 : (243617174297/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (243617174297/250000000000:ℝ) ≤ taylorCos (2264539139/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (975533796791/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1108301119/5000000000:ℝ) + taylorErr ≤ (975533796791/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (3435148867/15625000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (3435148867/15625000000:ℝ) ≤ taylorSin (1108301119/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (56130848697/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2264539139/10000000000:ℝ) + taylorErr ≤ (56130848697/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (243617174297/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (975533796791/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (3435148867/15625000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (56130848697/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (199812981847/15625000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12792824528171/1000000000000:ℝ) := by nlinarith
  have hp1 : (21164172896133/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21172106730223/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4652933410889/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1188408319471/250000000000:ℝ) := by nlinarith
  have hN : (1838699807049/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (81578179704287/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1838699807049/500000000000:ℝ) (81578179704287/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (158753629/1250000000000:ℝ) ≤ ((1838699807049/500000000000:ℝ)/(81578179704287/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_943 (x : ℝ) (h₁ : (16673/4096:ℝ) ≤ x) (h₂ : x ≤ (33361/8192:ℝ)) : (253929443/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1108301119/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2274126519/10000000000:ℝ) := by nlinarith
  have hc1 : (487126495129/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (487126495129/500000000000:ℝ) ≤ taylorCos (2274126519/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (975533796791/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1108301119/5000000000:ℝ) + taylorErr ≤ (975533796791/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (3435148867/15625000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (3435148867/15625000000:ℝ) ≤ taylorSin (1108301119/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (56364387907/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2274126519/10000000000:ℝ) + taylorErr ≤ (56364387907/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (487126495129/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (975533796791/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (3435148867/15625000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (56364387907/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (199812981847/15625000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3198445816541/250000000000:ℝ) := by nlinarith
  have hp1 : (21164172896133/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21173693440263/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4652933410889/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1193442270491/250000000000:ℝ) := by nlinarith
  have hN : (1838699807049/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (81590445130789/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1838699807049/500000000000:ℝ) (81590445130789/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (253929443/2000000000000:ℝ) ≤ ((1838699807049/500000000000:ℝ)/(81590445130789/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_944 (x : ℝ) (h₁ : (16673/4096:ℝ) ≤ x) (h₂ : x ≤ (16683/4096:ℝ)) : (634442007/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1108301119/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1146650639/5000000000:ℝ) := by nlinarith
  have hc1 : (973818890081/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (973818890081/1000000000000:ℝ) ≤ taylorCos (1146650639/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (975533796791/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1108301119/5000000000:ℝ) + taylorErr ≤ (975533796791/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (3435148867/15625000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (3435148867/15625000000:ℝ) ≤ taylorSin (1108301119/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (975533796791/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (3435148867/15625000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (113662621323/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (199812981847/15625000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12795700742149/1000000000000:ℝ) := by nlinarith
  have hp1 : (21164172896133/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21176866860341/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4652933410889/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (481403639751/100000000000:ℝ) := by nlinarith
  have hN : (1838699807049/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (65291982993053/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1838699807049/500000000000:ℝ) (65291982993053/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (634442007/5000000000000:ℝ) ≤ ((1838699807049/500000000000:ℝ)/(65291982993053/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_945 (x : ℝ) (h₁ : (16673/4096:ℝ) ≤ x) (h₂ : x ≤ (33371/8192:ℝ)) : (634060693/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1108301119/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1156238019/5000000000:ℝ) := by nlinarith
  have hc1 : (973381209429/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (973381209429/1000000000000:ℝ) ≤ taylorCos (1156238019/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (975533796791/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1108301119/5000000000:ℝ) + taylorErr ≤ (975533796791/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (3435148867/15625000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (3435148867/15625000000:ℝ) ≤ taylorSin (1108301119/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (975533796791/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (3435148867/15625000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (229192097951/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (199812981847/15625000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12797618218133/1000000000000:ℝ) := by nlinarith
  have hp1 : (21164172896133/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21180040280417/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4652933410889/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1213574466639/250000000000:ℝ) := by nlinarith
  have hN : (1838699807049/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (16327903205709/50000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1838699807049/500000000000:ℝ) (16327903205709/50000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (634060693/5000000000000:ℝ) ≤ ((1838699807049/500000000000:ℝ)/(16327903205709/50000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_946 (x : ℝ) (h₁ : (16673/4096:ℝ) ≤ x) (h₂ : x ≤ (1043/256:ℝ)) : (1267359331/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1108301119/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1165825399/5000000000:ℝ) := by nlinarith
  have hc1 : (486469974967/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (486469974967/500000000000:ℝ) ≤ taylorCos (1165825399/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (975533796791/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1108301119/5000000000:ℝ) + taylorErr ≤ (975533796791/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (3435148867/15625000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (3435148867/15625000000:ℝ) ≤ taylorSin (1108301119/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (975533796791/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (3435148867/15625000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (231058110583/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (199812981847/15625000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6399767847059/500000000000:ℝ) := by nlinarith
  have hp1 : (21164172896133/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10591606850247/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4652933410889/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (4894553333713/1000000000000:ℝ) := by nlinarith
  have hN : (1838699807049/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (163328113985001/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1838699807049/500000000000:ℝ) (163328113985001/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1267359331/10000000000000:ℝ) ≤ ((1838699807049/500000000000:ℝ)/(163328113985001/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_947 (x : ℝ) (h₁ : (16673/4096:ℝ) ≤ x) (h₂ : x ≤ (16693/4096:ℝ)) : (1265836939/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1108301119/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1185000159/5000000000:ℝ) := by nlinarith
  have hc1 : (243011675229/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (243011675229/250000000000:ℝ) ≤ taylorCos (1185000159/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (975533796791/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1108301119/5000000000:ℝ) + taylorErr ≤ (975533796791/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (3435148867/15625000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (3435148867/15625000000:ℝ) ≤ taylorSin (1108301119/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (975533796791/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (3435148867/15625000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (117393790193/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (199812981847/15625000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1600421330761/125000000000:ℝ) := by nlinarith
  have hp1 : (21164172896133/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21189560540649/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4652933410889/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (2487522824391/500000000000:ℝ) := by nlinarith
  have hN : (1838699807049/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (40856574975277/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1838699807049/500000000000:ℝ) (40856574975277/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1265836939/10000000000000:ℝ) ≤ ((1838699807049/500000000000:ℝ)/(40856574975277/125000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_948 (x : ℝ) (h₁ : (16673/4096:ℝ) ≤ x) (h₂ : x ≤ (8349/2048:ℝ)) : (1264316833/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1108301119/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2408349837/10000000000:ℝ) := by nlinarith
  have hc1 : (971139156187/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (971139156187/1000000000000:ℝ) ≤ taylorCos (2408349837/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (975533796791/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1108301119/5000000000:ℝ) + taylorErr ≤ (975533796791/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (3435148867/15625000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (3435148867/15625000000:ℝ) ≤ taylorSin (1108301119/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (975533796791/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (3435148867/15625000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (59628399277/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (199812981847/15625000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6403602799029/500000000000:ℝ) := by nlinarith
  have hp1 : (21164172896133/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (4239181476161/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4652933410889/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1263878028341/250000000000:ℝ) := by nlinarith
  have hN : (1838699807049/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (327049030461857/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1838699807049/500000000000:ℝ) (327049030461857/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1264316833/10000000000000:ℝ) ≤ ((1838699807049/500000000000:ℝ)/(327049030461857/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_949 (x : ℝ) (h₁ : (66697/16384:ℝ) ≤ x) (h₂ : x ≤ (66717/16384:ℝ)) : (1284126783/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1113094809/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2264539139/10000000000:ℝ) := by nlinarith
  have hc1 : (243617174297/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (243617174297/250000000000:ℝ) ≤ taylorCos (2264539139/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (48766128519/50000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1113094809/5000000000:ℝ) + taylorErr ≤ (48766128519/50000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (27598088453/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (27598088453/125000000000:ℝ) ≤ taylorSin (1113094809/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (56130848697/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2264539139/10000000000:ℝ) + taylorErr ≤ (56130848697/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (243617174297/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (48766128519/50000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (27598088453/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (56130848697/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12788989576201/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12792824528171/1000000000000:ℝ) := by nlinarith
  have hp1 : (2645719950769/125000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21172106730223/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1168269011571/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1188408319471/250000000000:ℝ) := by nlinarith
  have hN : (57777398061/15625000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (81578179704287/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (57777398061/15625000000:ℝ) (81578179704287/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1284126783/10000000000000:ℝ) ≤ ((57777398061/15625000000:ℝ)/(81578179704287/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_950 (x : ℝ) (h₁ : (66697/16384:ℝ) ≤ x) (h₂ : x ≤ (33361/8192:ℝ)) : (1283740729/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1113094809/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2274126519/10000000000:ℝ) := by nlinarith
  have hc1 : (487126495129/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (487126495129/500000000000:ℝ) ≤ taylorCos (2274126519/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (48766128519/50000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1113094809/5000000000:ℝ) + taylorErr ≤ (48766128519/50000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (27598088453/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (27598088453/125000000000:ℝ) ≤ taylorSin (1113094809/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (56364387907/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2274126519/10000000000:ℝ) + taylorErr ≤ (56364387907/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (487126495129/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (48766128519/50000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (27598088453/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (56364387907/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12788989576201/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3198445816541/250000000000:ℝ) := by nlinarith
  have hp1 : (2645719950769/125000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21173693440263/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1168269011571/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1193442270491/250000000000:ℝ) := by nlinarith
  have hN : (57777398061/15625000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (81590445130789/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (57777398061/15625000000:ℝ) (81590445130789/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1283740729/10000000000000:ℝ) ≤ ((57777398061/15625000000:ℝ)/(81590445130789/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_951 (x : ℝ) (h₁ : (33351/8192:ℝ) ≤ x) (h₂ : x ≤ (33361/8192:ℝ)) : (1297911731/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1117888499/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2274126519/10000000000:ℝ) := by nlinarith
  have hc1 : (487126495129/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (487126495129/500000000000:ℝ) ≤ taylorCos (2274126519/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (487555223737/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1117888499/5000000000:ℝ) + taylorErr ≤ (487555223737/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (110859842409/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (110859842409/500000000000:ℝ) ≤ taylorSin (1117888499/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (56364387907/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2274126519/10000000000:ℝ) + taylorErr ≤ (56364387907/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (487126495129/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (487555223737/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (110859842409/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (56364387907/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12789948314193/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3198445816541/250000000000:ℝ) := by nlinarith
  have hp1 : (2645918289521/125000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21173693440263/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2346608676827/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1193442270491/250000000000:ℝ) := by nlinarith
  have hN : (185905345309/50000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (81590445130789/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (185905345309/50000000000:ℝ) (81590445130789/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1297911731/10000000000000:ℝ) ≤ ((185905345309/50000000000:ℝ)/(81590445130789/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_952 (x : ℝ) (h₁ : (33351/8192:ℝ) ≤ x) (h₂ : x ≤ (66727/16384:ℝ)) : (648760781/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1117888499/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1141856949/5000000000:ℝ) := by nlinarith
  have hc1 : (974036387837/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (974036387837/1000000000000:ℝ) ≤ taylorCos (1141856949/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (487555223737/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1117888499/5000000000:ℝ) + taylorErr ≤ (487555223737/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (110859842409/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (110859842409/500000000000:ℝ) ≤ taylorSin (1117888499/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (487555223737/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (110859842409/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (14149468821/62500000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12789948314193/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3198685501039/250000000000:ℝ) := by nlinarith
  have hp1 : (2645918289521/125000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21175280150301/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2346608676827/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (2396951730101/500000000000:ℝ) := by nlinarith
  have hN : (185905345309/50000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (81602711476457/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (185905345309/50000000000:ℝ) (81602711476457/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (648760781/5000000000000:ℝ) ≤ ((185905345309/50000000000:ℝ)/(81602711476457/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_953 (x : ℝ) (h₁ : (33351/8192:ℝ) ≤ x) (h₂ : x ≤ (16683/4096:ℝ)) : (1297131539/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1117888499/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1146650639/5000000000:ℝ) := by nlinarith
  have hc1 : (973818890081/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (973818890081/1000000000000:ℝ) ≤ taylorCos (1146650639/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (487555223737/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1117888499/5000000000:ℝ) + taylorErr ≤ (487555223737/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (110859842409/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (110859842409/500000000000:ℝ) ≤ taylorSin (1117888499/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (487555223737/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (110859842409/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (113662621323/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12789948314193/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12795700742149/1000000000000:ℝ) := by nlinarith
  have hp1 : (2645918289521/125000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21176866860341/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2346608676827/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (481403639751/100000000000:ℝ) := by nlinarith
  have hN : (185905345309/50000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (65291982993053/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (185905345309/50000000000:ℝ) (65291982993053/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1297131539/10000000000000:ℝ) ≤ ((185905345309/50000000000:ℝ)/(65291982993053/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_954 (x : ℝ) (h₁ : (33351/8192:ℝ) ≤ x) (h₂ : x ≤ (33371/8192:ℝ)) : (648175967/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1117888499/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1156238019/5000000000:ℝ) := by nlinarith
  have hc1 : (973381209429/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (973381209429/1000000000000:ℝ) ≤ taylorCos (1156238019/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (487555223737/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1117888499/5000000000:ℝ) + taylorErr ≤ (487555223737/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (110859842409/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (110859842409/500000000000:ℝ) ≤ taylorSin (1117888499/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (487555223737/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (110859842409/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (229192097951/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12789948314193/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12797618218133/1000000000000:ℝ) := by nlinarith
  have hp1 : (2645918289521/125000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21180040280417/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2346608676827/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1213574466639/250000000000:ℝ) := by nlinarith
  have hN : (185905345309/50000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (16327903205709/50000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (185905345309/50000000000:ℝ) (16327903205709/50000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (648175967/5000000000000:ℝ) ≤ ((185905345309/50000000000:ℝ)/(16327903205709/50000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_955 (x : ℝ) (h₁ : (33351/8192:ℝ) ≤ x) (h₂ : x ≤ (1043/256:ℝ)) : (647786457/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1117888499/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1165825399/5000000000:ℝ) := by nlinarith
  have hc1 : (486469974967/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (486469974967/500000000000:ℝ) ≤ taylorCos (1165825399/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (487555223737/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1117888499/5000000000:ℝ) + taylorErr ≤ (487555223737/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (110859842409/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (110859842409/500000000000:ℝ) ≤ taylorSin (1117888499/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (487555223737/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (110859842409/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (231058110583/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12789948314193/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6399767847059/500000000000:ℝ) := by nlinarith
  have hp1 : (2645918289521/125000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10591606850247/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2346608676827/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (4894553333713/1000000000000:ℝ) := by nlinarith
  have hN : (185905345309/50000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (163328113985001/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (185905345309/50000000000:ℝ) (163328113985001/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (647786457/5000000000000:ℝ) ≤ ((185905345309/50000000000:ℝ)/(163328113985001/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_956 (x : ℝ) (h₁ : (4169/1024:ℝ) ≤ x) (h₂ : x ≤ (265/64:ℝ)) : (1219525351/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (44792239/200000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (441786467/1000000000:ℝ) := by nlinarith
  have hc1 : (903989290823/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (903989290823/1000000000000:ℝ) ≤ taylorCos (441786467/1000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (121878168417/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (44792239/200000000:ℝ) + taylorErr ≤ (121878168417/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (222093618681/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (222093618681/1000000000000:ℝ) ≤ taylorSin (44792239/200000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (427555095773/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (441786467/1000000000:ℝ) + taylorErr ≤ (427555095773/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (903989290823/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (121878168417/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (222093618681/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (427555095773/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1279033180939/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (13008157081271/1000000000000:ℝ) := by nlinarith
  have hp1 : (846719240007/40000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21528481804913/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4701273500499/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (9204612099947/1000000000000:ℝ) := by nlinarith
  have hN : (3726248153163/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (168712150651021/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3726248153163/1000000000000:ℝ) (168712150651021/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1219525351/10000000000000:ℝ) ≤ ((3726248153163/1000000000000:ℝ)/(168712150651021/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_957 (x : ℝ) (h₁ : (66707/16384:ℝ) ≤ x) (h₂ : x ≤ (33361/8192:ℝ)) : (328040051/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1122682189/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2274126519/10000000000:ℝ) := by nlinarith
  have hc1 : (487126495129/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (487126495129/500000000000:ℝ) ≤ taylorCos (2274126519/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (974897428267/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1122682189/5000000000:ℝ) + taylorErr ≤ (974897428267/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (222654458213/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (222654458213/1000000000000:ℝ) ≤ taylorSin (1122682189/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (56364387907/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2274126519/10000000000:ℝ) + taylorErr ≤ (56364387907/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (487126495129/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (974897428267/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (222654458213/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (56364387907/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (2558181410437/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3198445816541/250000000000:ℝ) := by nlinarith
  have hp1 : (4233786605237/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21173693440263/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1178339328473/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1193442270491/250000000000:ℝ) := by nlinarith
  have hN : (5981535817/1600000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (81590445130789/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (5981535817/1600000000:ℝ) (81590445130789/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (328040051/2500000000000:ℝ) ≤ ((5981535817/1600000000:ℝ)/(81590445130789/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_958 (x : ℝ) (h₁ : (66707/16384:ℝ) ≤ x) (h₂ : x ≤ (66727/16384:ℝ)) : (1311765751/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1122682189/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1141856949/5000000000:ℝ) := by nlinarith
  have hc1 : (974036387837/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (974036387837/1000000000000:ℝ) ≤ taylorCos (1141856949/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (974897428267/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1122682189/5000000000:ℝ) + taylorErr ≤ (974897428267/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (222654458213/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (222654458213/1000000000000:ℝ) ≤ taylorSin (1122682189/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (974897428267/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (222654458213/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (14149468821/62500000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (2558181410437/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3198685501039/250000000000:ℝ) := by nlinarith
  have hp1 : (4233786605237/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21175280150301/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1178339328473/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (2396951730101/500000000000:ℝ) := by nlinarith
  have hN : (5981535817/1600000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (81602711476457/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (5981535817/1600000000:ℝ) (81602711476457/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1311765751/10000000000000:ℝ) ≤ ((5981535817/1600000000:ℝ)/(81602711476457/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_959 (x : ℝ) (h₁ : (66707/16384:ℝ) ≤ x) (h₂ : x ≤ (16683/4096:ℝ)) : (1311371447/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1122682189/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1146650639/5000000000:ℝ) := by nlinarith
  have hc1 : (973818890081/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (973818890081/1000000000000:ℝ) ≤ taylorCos (1146650639/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (974897428267/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1122682189/5000000000:ℝ) + taylorErr ≤ (974897428267/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (222654458213/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (222654458213/1000000000000:ℝ) ≤ taylorSin (1122682189/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (974897428267/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (222654458213/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (113662621323/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (2558181410437/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12795700742149/1000000000000:ℝ) := by nlinarith
  have hp1 : (4233786605237/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21176866860341/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1178339328473/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (481403639751/100000000000:ℝ) := by nlinarith
  have hN : (5981535817/1600000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (65291982993053/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (5981535817/1600000000:ℝ) (65291982993053/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1311371447/10000000000000:ℝ) ≤ ((5981535817/1600000000:ℝ)/(65291982993053/200000000000:ℝ))^2 := by norm_num
  linarith

end Zeta23Ext.Bridge.FourPoint
