import FourPoint.Base

noncomputable section
open Real
namespace Zeta23Ext.Bridge.FourPoint


theorem wc_1020 (x : ℝ) (h₁ : (1043/256:ℝ) ≤ x) (h₂ : x ≤ (2101/512:ℝ)) : (140043451/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2331650797/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (3252039271/10000000000:ℝ) := by nlinarith
  have hc1 : (473792794367/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (473792794367/500000000000:ℝ) ≤ taylorCos (3252039271/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (972939954481/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2331650797/10000000000:ℝ) + taylorErr ≤ (972939954481/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (231058105961/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (231058105961/1000000000000:ℝ) ≤ taylorSin (2331650797/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (319502033143/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3252039271/10000000000:ℝ) + taylorErr ≤ (319502033143/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (473792794367/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (972939954481/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (231058105961/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (319502033143/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12799535694117/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12891574541391/1000000000000:ℝ) := by nlinarith
  have hp1 : (10591606708171/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1333471116513/62500000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4894553170147/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (3408373862907/500000000000:ℝ) := by nlinarith
  have hN : (1960806607833/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (165692694156241/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1960806607833/500000000000:ℝ) (165692694156241/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (140043451/1000000000000:ℝ) ≤ ((1960806607833/500000000000:ℝ)/(165692694156241/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1021 (x : ℝ) (h₁ : (1043/256:ℝ) ≤ x) (h₂ : x ≤ (1053/256:ℝ)) : (69357131/500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2331650797/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (889708857/2500000000:ℝ) := by nlinarith
  have hc1 : (937339009647/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (937339009647/1000000000000:ℝ) ≤ taylorCos (889708857/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (972939954481/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2331650797/10000000000:ℝ) + taylorErr ≤ (972939954481/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (231058105961/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (231058105961/1000000000000:ℝ) ≤ taylorSin (2331650797/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (348418682521/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (889708857/2500000000:ℝ) + taylorErr ≤ (348418682521/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (937339009647/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (972939954481/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (231058105961/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (348418682521/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12799535694117/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12922254157149/1000000000000:ℝ) := by nlinarith
  have hp1 : (10591606708171/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10693156292723/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4894553170147/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1862847713751/250000000000:ℝ) := by nlinarith
  have hN : (1960806607833/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (33296930500391/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1960806607833/500000000000:ℝ) (33296930500391/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (69357131/500000000000:ℝ) ≤ ((1960806607833/500000000000:ℝ)/(33296930500391/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1022 (x : ℝ) (h₁ : (1043/256:ℝ) ≤ x) (h₂ : x ≤ (2111/512:ℝ)) : (274801629/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2331650797/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1932815793/5000000000:ℝ) := by nlinarith
  have hc1 : (57888139991/62500000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (57888139991/62500000000:ℝ) ≤ taylorCos (1932815793/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (972939954481/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2331650797/10000000000:ℝ) + taylorErr ≤ (972939954481/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (231058105961/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (231058105961/1000000000000:ℝ) ≤ taylorSin (2331650797/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (377007412527/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1932815793/5000000000:ℝ) + taylorErr ≤ (377007412527/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (57888139991/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (972939954481/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (231058105961/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (377007412527/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12799535694117/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12952933772907/1000000000000:ℝ) := by nlinarith
  have hp1 : (10591606708171/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (4287417461337/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4894553170147/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (8081940817609/1000000000000:ℝ) := by nlinarith
  have hN : (1960806607833/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (33455698665063/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1960806607833/500000000000:ℝ) (33455698665063/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (274801629/2000000000000:ℝ) ≤ ((1960806607833/500000000000:ℝ)/(33455698665063/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1023 (x : ℝ) (h₁ : (1043/256:ℝ) ≤ x) (h₂ : x ≤ (529/128:ℝ)) : (1361028853/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2331650797/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (130388367/312500000:ℝ) := by nlinarith
  have hc1 : (914209753403/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (914209753403/1000000000000:ℝ) ≤ taylorCos (130388367/312500000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (972939954481/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2331650797/10000000000:ℝ) + taylorErr ≤ (972939954481/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (231058105961/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (231058105961/1000000000000:ℝ) ≤ taylorSin (2331650797/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (202620658177/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (130388367/312500000:ℝ) + taylorErr ≤ (202620658177/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (914209753403/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (972939954481/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (231058105961/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (202620658177/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12799535694117/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2596722677733/200000000000:ℝ) := by nlinarith
  have hp1 : (10591606708171/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21487862027923/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4894553170147/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (8707769493829/1000000000000:ℝ) := by nlinarith
  have hN : (1960806607833/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (336148433252643/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1960806607833/500000000000:ℝ) (336148433252643/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1361028853/10000000000000:ℝ) ≤ ((1960806607833/500000000000:ℝ)/(336148433252643/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1024 (x : ℝ) (h₁ : (1043/256:ℝ) ≤ x) (h₂ : x ≤ (1063/256:ℝ)) : (1335527067/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2331650797/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (4786020059/10000000000:ℝ) := by nlinarith
  have hc1 : (110954952263/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (110954952263/125000000000:ℝ) ≤ taylorCos (4786020059/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (972939954481/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2331650797/10000000000:ℝ) + taylorErr ≤ (972939954481/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (231058105961/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (231058105961/1000000000000:ℝ) ≤ taylorSin (2331650797/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (460538713291/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (4786020059/10000000000:ℝ) + taylorErr ≤ (460538713291/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (110954952263/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (972939954481/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (231058105961/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (460538713291/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12799535694117/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (652248631009/50000000000:ℝ) := by nlinarith
  have hp1 : (10591606708171/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21589411470399/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4894553170147/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1242844972411/125000000000:ℝ) := by nlinarith
  have hN : (1960806607833/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (84835655330623/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1960806607833/500000000000:ℝ) (84835655330623/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1335527067/10000000000000:ℝ) ≤ ((1960806607833/500000000000:ℝ)/(84835655330623/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1025 (x : ℝ) (h₁ : (1043/256:ℝ) ≤ x) (h₂ : x ≤ (267/64:ℝ)) : (655310061/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2331650797/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2699806187/5000000000:ℝ) := by nlinarith
  have hc1 : (107216075963/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (107216075963/125000000000:ℝ) ≤ taylorCos (2699806187/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (972939954481/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2331650797/10000000000:ℝ) + taylorErr ≤ (972939954481/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (231058105961/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (231058105961/1000000000000:ℝ) ≤ taylorSin (2331650797/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (51410274651/100000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2699806187/5000000000:ℝ) + taylorErr ≤ (51410274651/100000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (107216075963/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (972939954481/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (231058105961/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (51410274651/100000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12799535694117/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2621266370339/200000000000:ℝ) := by nlinarith
  have hp1 : (10591606708171/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10845480456437/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4894553170147/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (44605530319/4000000000:ℝ) := by nlinarith
  have hN : (1960806607833/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (34255186921351/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1960806607833/500000000000:ℝ) (34255186921351/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (655310061/5000000000000:ℝ) ≤ ((1960806607833/500000000000:ℝ)/(34255186921351/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1026 (x : ℝ) (h₁ : (66757/16384:ℝ) ≤ x) (h₂ : x ≤ (16693/4096:ℝ)) : (363630819/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2341238177/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1185000159/5000000000:ℝ) := by nlinarith
  have hc1 : (243011675229/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (243011675229/250000000000:ℝ) ≤ taylorCos (1185000159/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (486358991587/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2341238177/10000000000:ℝ) + taylorErr ≤ (486358991587/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (231990794131/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (231990794131/1000000000000:ℝ) ≤ taylorSin (2341238177/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (486358991587/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (231990794131/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (117393790193/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1280049443211/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1600421330761/125000000000:ℝ) := by nlinarith
  have hp1 : (529620003159/25000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21189560540649/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (245733930241/50000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (2487522824391/500000000000:ℝ) := by nlinarith
  have hN : (1970980310823/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (40856574975277/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1970980310823/500000000000:ℝ) (40856574975277/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (363630819/2500000000000:ℝ) ≤ ((1970980310823/500000000000:ℝ)/(40856574975277/125000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1027 (x : ℝ) (h₁ : (66757/16384:ℝ) ≤ x) (h₂ : x ≤ (66777/16384:ℝ)) : (1454086357/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2341238177/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1189793849/5000000000:ℝ) := by nlinarith
  have hc1 : (194364230887/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (194364230887/200000000000:ℝ) ≤ taylorCos (1189793849/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (486358991587/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2341238177/10000000000:ℝ) + taylorErr ≤ (486358991587/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (231990794131/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (231990794131/1000000000000:ℝ) ≤ taylorSin (2341238177/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (486358991587/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (231990794131/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (235719410449/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1280049443211/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (160054117301/12500000000:ℝ) := by nlinarith
  have hp1 : (529620003159/25000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21191147250687/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (245733930241/50000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (499516473667/100000000000:ℝ) := by nlinarith
  have hN : (1970980310823/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (32690170195203/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1970980310823/500000000000:ℝ) (32690170195203/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1454086357/10000000000000:ℝ) ≤ ((1970980310823/500000000000:ℝ)/(32690170195203/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1028 (x : ℝ) (h₁ : (66757/16384:ℝ) ≤ x) (h₂ : x ≤ (33391/8192:ℝ)) : (726824801/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2341238177/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1194587539/5000000000:ℝ) := by nlinarith
  have hc1 : (971594714677/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (971594714677/1000000000000:ℝ) ≤ taylorCos (1194587539/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (486358991587/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2341238177/10000000000:ℝ) + taylorErr ≤ (486358991587/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (231990794131/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (231990794131/1000000000000:ℝ) ≤ taylorSin (2341238177/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (486358991587/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (231990794131/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (47330204769/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1280049443211/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12805288122073/1000000000000:ℝ) := by nlinarith
  have hp1 : (529620003159/25000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21192733960727/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (245733930241/50000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (5015282189881/1000000000000:ℝ) := by nlinarith
  have hN : (1970980310823/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20434425486163/62500000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1970980310823/500000000000:ℝ) (20434425486163/62500000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (726824801/5000000000000:ℝ) ≤ ((1970980310823/500000000000:ℝ)/(20434425486163/62500000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1029 (x : ℝ) (h₁ : (33381/8192:ℝ) ≤ x) (h₂ : x ≤ (66777/16384:ℝ)) : (73456793/500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2350825557/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1189793849/5000000000:ℝ) := by nlinarith
  have hc1 : (194364230887/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (194364230887/200000000000:ℝ) ≤ taylorCos (1189793849/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (194499023553/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2350825557/10000000000:ℝ) + taylorErr ≤ (194499023553/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (232923269059/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (232923269059/1000000000000:ℝ) ≤ taylorSin (2350825557/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (194499023553/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (232923269059/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (235719410449/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6400726585051/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (160054117301/12500000000:ℝ) := by nlinarith
  have hp1 : (21186386836377/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21191147250687/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4934802481477/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (499516473667/100000000000:ℝ) := by nlinarith
  have hN : (30955526279/7812500000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (32690170195203/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (30955526279/7812500000:ℝ) (32690170195203/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (73456793/500000000000:ℝ) ≤ ((30955526279/7812500000:ℝ)/(32690170195203/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1030 (x : ℝ) (h₁ : (33381/8192:ℝ) ≤ x) (h₂ : x ≤ (33391/8192:ℝ)) : (293738917/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2350825557/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1194587539/5000000000:ℝ) := by nlinarith
  have hc1 : (971594714677/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (971594714677/1000000000000:ℝ) ≤ taylorCos (1194587539/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (194499023553/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2350825557/10000000000:ℝ) + taylorErr ≤ (194499023553/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (232923269059/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (232923269059/1000000000000:ℝ) ≤ taylorSin (2350825557/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (194499023553/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (232923269059/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (47330204769/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6400726585051/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12805288122073/1000000000000:ℝ) := by nlinarith
  have hp1 : (21186386836377/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21192733960727/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4934802481477/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (5015282189881/1000000000000:ℝ) := by nlinarith
  have hN : (30955526279/7812500000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20434425486163/62500000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (30955526279/7812500000:ℝ) (20434425486163/62500000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (293738917/2000000000000:ℝ) ≤ ((30955526279/7812500000:ℝ)/(20434425486163/62500000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1031 (x : ℝ) (h₁ : (33381/8192:ℝ) ≤ x) (h₂ : x ≤ (66787/16384:ℝ)) : (58730139/400000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2350825557/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1199381229/5000000000:ℝ) := by nlinarith
  have hc1 : (19427347637/20000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (19427347637/20000000000:ℝ) ≤ taylorCos (1199381229/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (194499023553/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2350825557/10000000000:ℝ) + taylorErr ≤ (194499023553/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (232923269059/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (232923269059/1000000000000:ℝ) ≤ taylorSin (2350825557/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (47516483943/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1199381229/5000000000:ℝ) + taylorErr ≤ (47516483943/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (19427347637/20000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (194499023553/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (232923269059/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (47516483943/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6400726585051/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2561249372013/200000000000:ℝ) := by nlinarith
  have hp1 : (21186386836377/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (4238864134153/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4934802481477/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (629424748647/125000000000:ℝ) := by nlinarith
  have hN : (30955526279/7812500000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (6539998345637/20000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (30955526279/7812500000:ℝ) (6539998345637/20000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (58730139/400000000000:ℝ) ≤ ((30955526279/7812500000:ℝ)/(6539998345637/20000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1032 (x : ℝ) (h₁ : (33381/8192:ℝ) ≤ x) (h₂ : x ≤ (8349/2048:ℝ)) : (1467812531/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2350825557/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2408349837/10000000000:ℝ) := by nlinarith
  have hc1 : (971139156187/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (971139156187/1000000000000:ℝ) ≤ taylorCos (2408349837/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (194499023553/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2350825557/10000000000:ℝ) + taylorErr ≤ (194499023553/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (232923269059/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (232923269059/1000000000000:ℝ) ≤ taylorSin (2350825557/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (194499023553/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (232923269059/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (59628399277/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6400726585051/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6403602799029/500000000000:ℝ) := by nlinarith
  have hp1 : (21186386836377/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (4239181476161/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4934802481477/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1263878028341/250000000000:ℝ) := by nlinarith
  have hN : (30955526279/7812500000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (327049030461857/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (30955526279/7812500000:ℝ) (327049030461857/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1467812531/10000000000000:ℝ) ≤ ((30955526279/7812500000:ℝ)/(327049030461857/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1033 (x : ℝ) (h₁ : (33381/8192:ℝ) ≤ x) (h₂ : x ≤ (33401/8192:ℝ)) : (1466931139/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2350825557/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2427524597/10000000000:ℝ) := by nlinarith
  have hc1 : (485340013537/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (485340013537/500000000000:ℝ) ≤ taylorCos (2427524597/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (194499023553/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2350825557/10000000000:ℝ) + taylorErr ≤ (194499023553/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (232923269059/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (232923269059/1000000000000:ℝ) ≤ taylorSin (2350825557/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (194499023553/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (232923269059/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (240375293523/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6400726585051/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12809123074043/1000000000000:ℝ) := by nlinarith
  have hp1 : (21186386836377/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10599540400441/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4934802481477/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (509573526993/100000000000:ℝ) := by nlinarith
  have hN : (30955526279/7812500000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (163573633925981/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (30955526279/7812500000:ℝ) (163573633925981/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1466931139/10000000000000:ℝ) ≤ ((30955526279/7812500000:ℝ)/(163573633925981/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1034 (x : ℝ) (h₁ : (33381/8192:ℝ) ≤ x) (h₂ : x ≤ (16703/4096:ℝ)) : (1466050409/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2350825557/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2446699357/10000000000:ℝ) := by nlinarith
  have hc1 : (121277166131/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (121277166131/125000000000:ℝ) ≤ taylorCos (2446699357/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (194499023553/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2350825557/10000000000:ℝ) + taylorErr ≤ (194499023553/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (232923269059/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (232923269059/1000000000000:ℝ) ≤ taylorSin (2350825557/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (194499023553/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (232923269059/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (242236106147/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6400726585051/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12811040550027/1000000000000:ℝ) := by nlinarith
  have hp1 : (21186386836377/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10601127110479/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (4934802481477/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (641993938003/125000000000:ℝ) := by nlinarith
  have hN : (30955526279/7812500000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (327245519948873/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (30955526279/7812500000:ℝ) (327245519948873/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1466050409/10000000000000:ℝ) ≤ ((30955526279/7812500000:ℝ)/(327245519948873/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1035 (x : ℝ) (h₁ : (66767/16384:ℝ) ≤ x) (h₂ : x ≤ (33391/8192:ℝ)) : (296763303/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2360412937/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1194587539/5000000000:ℝ) := by nlinarith
  have hc1 : (971594714677/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (971594714677/1000000000000:ℝ) ≤ taylorCos (1194587539/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (48613567923/50000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2360412937/10000000000:ℝ) + taylorErr ≤ (48613567923/50000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (233855529889/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (233855529889/1000000000000:ℝ) ≤ taylorSin (2360412937/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (48613567923/50000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (233855529889/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (47330204769/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (2560482381619/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12805288122073/1000000000000:ℝ) := by nlinarith
  have hp1 : (4237594709279/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21192733960727/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2477462390483/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (5015282189881/1000000000000:ℝ) := by nlinarith
  have hN : (1991326711253/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20434425486163/62500000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1991326711253/500000000000:ℝ) (20434425486163/62500000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (296763303/2000000000000:ℝ) ≤ ((1991326711253/500000000000:ℝ)/(20434425486163/62500000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1036 (x : ℝ) (h₁ : (66767/16384:ℝ) ≤ x) (h₂ : x ≤ (66787/16384:ℝ)) : (1483370863/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2360412937/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1199381229/5000000000:ℝ) := by nlinarith
  have hc1 : (19427347637/20000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (19427347637/20000000000:ℝ) ≤ taylorCos (1199381229/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (48613567923/50000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2360412937/10000000000:ℝ) + taylorErr ≤ (48613567923/50000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (233855529889/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (233855529889/1000000000000:ℝ) ≤ taylorSin (2360412937/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (47516483943/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1199381229/5000000000:ℝ) + taylorErr ≤ (47516483943/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (19427347637/20000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (48613567923/50000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (233855529889/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (47516483943/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (2560482381619/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2561249372013/200000000000:ℝ) := by nlinarith
  have hp1 : (4237594709279/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (4238864134153/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2477462390483/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (629424748647/125000000000:ℝ) := by nlinarith
  have hN : (1991326711253/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (6539998345637/20000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1991326711253/500000000000:ℝ) (6539998345637/20000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1483370863/10000000000000:ℝ) ≤ ((1991326711253/500000000000:ℝ)/(6539998345637/20000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1037 (x : ℝ) (h₁ : (66767/16384:ℝ) ≤ x) (h₂ : x ≤ (8349/2048:ℝ)) : (1482925379/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2360412937/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2408349837/10000000000:ℝ) := by nlinarith
  have hc1 : (971139156187/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (971139156187/1000000000000:ℝ) ≤ taylorCos (2408349837/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (48613567923/50000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2360412937/10000000000:ℝ) + taylorErr ≤ (48613567923/50000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (233855529889/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (233855529889/1000000000000:ℝ) ≤ taylorSin (2360412937/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (48613567923/50000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (233855529889/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (59628399277/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (2560482381619/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6403602799029/500000000000:ℝ) := by nlinarith
  have hp1 : (4237594709279/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (4239181476161/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2477462390483/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1263878028341/250000000000:ℝ) := by nlinarith
  have hN : (1991326711253/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (327049030461857/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1991326711253/500000000000:ℝ) (327049030461857/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1482925379/10000000000000:ℝ) ≤ ((1991326711253/500000000000:ℝ)/(327049030461857/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1038 (x : ℝ) (h₁ : (16693/4096:ℝ) ≤ x) (h₂ : x ≤ (66787/16384:ℝ)) : (1498565153/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2370000317/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1199381229/5000000000:ℝ) := by nlinarith
  have hc1 : (19427347637/20000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (19427347637/20000000000:ℝ) ≤ taylorCos (1199381229/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (972046705463/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2370000317/10000000000:ℝ) + taylorErr ≤ (972046705463/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (58696893941/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (58696893941/250000000000:ℝ) ≤ taylorSin (2370000317/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (47516483943/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1199381229/5000000000:ℝ) + taylorErr ≤ (47516483943/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (19427347637/20000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (972046705463/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (58696893941/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (47516483943/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12803370646087/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2561249372013/200000000000:ℝ) := by nlinarith
  have hp1 : (5297390064103/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (4238864134153/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1243761371027/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (629424748647/125000000000:ℝ) := by nlinarith
  have hN : (800599755729/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (6539998345637/20000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (800599755729/200000000000:ℝ) (6539998345637/20000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1498565153/10000000000000:ℝ) ≤ ((800599755729/200000000000:ℝ)/(6539998345637/20000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1039 (x : ℝ) (h₁ : (16693/4096:ℝ) ≤ x) (h₂ : x ≤ (8349/2048:ℝ)) : (749057553/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2370000317/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2408349837/10000000000:ℝ) := by nlinarith
  have hc1 : (971139156187/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (971139156187/1000000000000:ℝ) ≤ taylorCos (2408349837/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (972046705463/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2370000317/10000000000:ℝ) + taylorErr ≤ (972046705463/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (58696893941/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (58696893941/250000000000:ℝ) ≤ taylorSin (2370000317/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (972046705463/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (58696893941/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (59628399277/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12803370646087/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6403602799029/500000000000:ℝ) := by nlinarith
  have hp1 : (5297390064103/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (4239181476161/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1243761371027/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1263878028341/250000000000:ℝ) := by nlinarith
  have hN : (800599755729/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (327049030461857/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (800599755729/200000000000:ℝ) (327049030461857/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (749057553/5000000000000:ℝ) ≤ ((800599755729/200000000000:ℝ)/(327049030461857/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1040 (x : ℝ) (h₁ : (16693/4096:ℝ) ≤ x) (h₂ : x ≤ (66797/16384:ℝ)) : (1497665227/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2370000317/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2417937217/10000000000:ℝ) := by nlinarith
  have hc1 : (19418200757/20000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (19418200757/20000000000:ℝ) ≤ taylorCos (2417937217/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (972046705463/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2370000317/10000000000:ℝ) + taylorErr ≤ (972046705463/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (58696893941/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (58696893941/250000000000:ℝ) ≤ taylorSin (2370000317/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (119722277681/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2417937217/10000000000:ℝ) + taylorErr ≤ (119722277681/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (19418200757/20000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (972046705463/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (58696893941/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (119722277681/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12803370646087/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (256163286721/20000000000:ℝ) := by nlinarith
  have hp1 : (5297390064103/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21197494090843/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1243761371027/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (5075624547371/1000000000000:ℝ) := by nlinarith
  have hN : (800599755729/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (327098147318527/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (800599755729/200000000000:ℝ) (327098147318527/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1497665227/10000000000000:ℝ) ≤ ((800599755729/200000000000:ℝ)/(327098147318527/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1041 (x : ℝ) (h₁ : (16693/4096:ℝ) ≤ x) (h₂ : x ≤ (33401/8192:ℝ)) : (748607759/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2370000317/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2427524597/10000000000:ℝ) := by nlinarith
  have hc1 : (485340013537/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (485340013537/500000000000:ℝ) ≤ taylorCos (2427524597/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (972046705463/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2370000317/10000000000:ℝ) + taylorErr ≤ (972046705463/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (58696893941/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (58696893941/250000000000:ℝ) ≤ taylorSin (2370000317/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (972046705463/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (58696893941/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (240375293523/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12803370646087/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12809123074043/1000000000000:ℝ) := by nlinarith
  have hp1 : (5297390064103/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10599540400441/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1243761371027/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (509573526993/100000000000:ℝ) := by nlinarith
  have hN : (800599755729/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (163573633925981/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (800599755729/200000000000:ℝ) (163573633925981/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (748607759/5000000000000:ℝ) ≤ ((800599755729/200000000000:ℝ)/(163573633925981/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1042 (x : ℝ) (h₁ : (16693/4096:ℝ) ≤ x) (h₂ : x ≤ (16703/4096:ℝ)) : (748158303/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2370000317/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2446699357/10000000000:ℝ) := by nlinarith
  have hc1 : (121277166131/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (121277166131/125000000000:ℝ) ≤ taylorCos (2446699357/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (972046705463/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2370000317/10000000000:ℝ) + taylorErr ≤ (972046705463/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (58696893941/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (58696893941/250000000000:ℝ) ≤ taylorSin (2370000317/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (972046705463/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (58696893941/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (242236106147/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12803370646087/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12811040550027/1000000000000:ℝ) := by nlinarith
  have hp1 : (5297390064103/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10601127110479/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1243761371027/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (641993938003/125000000000:ℝ) := by nlinarith
  have hN : (800599755729/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (327245519948873/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (800599755729/200000000000:ℝ) (327245519948873/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (748158303/5000000000000:ℝ) ≤ ((800599755729/200000000000:ℝ)/(327245519948873/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1043 (x : ℝ) (h₁ : (16693/4096:ℝ) ≤ x) (h₂ : x ≤ (33411/8192:ℝ)) : (1495418369/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2370000317/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2465874117/10000000000:ℝ) := by nlinarith
  have hc1 : (242437765953/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (242437765953/250000000000:ℝ) ≤ taylorCos (2465874117/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (972046705463/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2370000317/10000000000:ℝ) + taylorErr ≤ (972046705463/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (58696893941/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (58696893941/250000000000:ℝ) ≤ taylorSin (2370000317/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (122048014069/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2465874117/10000000000:ℝ) + taylorErr ≤ (122048014069/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (242437765953/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (972046705463/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (58696893941/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (122048014069/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12803370646087/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3203239506503/250000000000:ℝ) := by nlinarith
  have hp1 : (5297390064103/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5301356910259/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1243761371027/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1035232132429/200000000000:ℝ) := by nlinarith
  have hN : (800599755729/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (327343786752691/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (800599755729/200000000000:ℝ) (327343786752691/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1495418369/10000000000000:ℝ) ≤ ((800599755729/200000000000:ℝ)/(327343786752691/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1044 (x : ℝ) (h₁ : (16693/4096:ℝ) ≤ x) (h₂ : x ≤ (4177/1024:ℝ)) : (747260403/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2370000317/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2485048877/10000000000:ℝ) := by nlinarith
  have hc1 : (969281233079/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (969281233079/1000000000000:ℝ) ≤ taylorCos (2485048877/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (972046705463/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2370000317/10000000000:ℝ) + taylorErr ≤ (972046705463/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (58696893941/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (58696893941/250000000000:ℝ) ≤ taylorSin (2370000317/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (972046705463/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (58696893941/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (245955052659/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12803370646087/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12814875501997/1000000000000:ℝ) := by nlinarith
  have hp1 : (5297390064103/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21208601061113/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1243761371027/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (521636259081/100000000000:ℝ) := by nlinarith
  have hN : (800599755729/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (163721034131683/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (800599755729/200000000000:ℝ) (163721034131683/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (747260403/5000000000000:ℝ) ≤ ((800599755729/200000000000:ℝ)/(163721034131683/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1045 (x : ℝ) (h₁ : (16693/4096:ℝ) ≤ x) (h₂ : x ≤ (16713/4096:ℝ)) : (1492727701/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2370000317/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2523398397/10000000000:ℝ) := by nlinarith
  have hc1 : (968330882047/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (968330882047/1000000000000:ℝ) ≤ taylorCos (2523398397/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (972046705463/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2370000317/10000000000:ℝ) + taylorErr ≤ (972046705463/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (58696893941/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (58696893941/250000000000:ℝ) ≤ taylorSin (2370000317/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (972046705463/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (58696893941/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (249670381949/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12803370646087/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12818710453967/1000000000000:ℝ) := by nlinarith
  have hp1 : (5297390064103/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21214947901269/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1243761371027/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (2648372072769/500000000000:ℝ) := by nlinarith
  have hN : (800599755729/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (163819337702643/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (800599755729/200000000000:ℝ) (163819337702643/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1492727701/10000000000000:ℝ) ≤ ((800599755729/200000000000:ℝ)/(163819337702643/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1046 (x : ℝ) (h₁ : (16693/4096:ℝ) ≤ x) (h₂ : x ≤ (8359/2048:ℝ)) : (298187457/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2370000317/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (640436979/2500000000:ℝ) := by nlinarith
  have hc1 : (483683144977/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (483683144977/500000000000:ℝ) ≤ taylorCos (640436979/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (972046705463/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2370000317/10000000000:ℝ) + taylorErr ≤ (972046705463/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (58696893941/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (58696893941/250000000000:ℝ) ≤ taylorSin (2370000317/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (972046705463/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (58696893941/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (3167275491/12500000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12803370646087/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12822545405937/1000000000000:ℝ) := by nlinarith
  have hp1 : (5297390064103/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1326330921339/62500000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1243761371027/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (336068433609/62500000000:ℝ) := by nlinarith
  have hN : (800599755729/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (327835341374633/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (800599755729/200000000000:ℝ) (327835341374633/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (298187457/2000000000000:ℝ) ≤ ((800599755729/200000000000:ℝ)/(327835341374633/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1047 (x : ℝ) (h₁ : (66777/16384:ℝ) ≤ x) (h₂ : x ≤ (8349/2048:ℝ)) : (189172711/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2379587697/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2408349837/10000000000:ℝ) := by nlinarith
  have hc1 : (971139156187/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (971139156187/1000000000000:ℝ) ≤ taylorCos (2408349837/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (971821158983/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2379587697/10000000000:ℝ) + taylorErr ≤ (971821158983/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (58929851457/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (58929851457/250000000000:ℝ) ≤ taylorSin (2379587697/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (971821158983/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (58929851457/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (59628399277/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12804329384079/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6403602799029/500000000000:ℝ) := by nlinarith
  have hp1 : (21191146966429/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (4239181476161/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (249758228587/50000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1263878028341/250000000000:ℝ) := by nlinarith
  have hN : (4023343412757/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (327049030461857/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4023343412757/1000000000000:ℝ) (327049030461857/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (189172711/1250000000000:ℝ) ≤ ((4023343412757/1000000000000:ℝ)/(327049030461857/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1048 (x : ℝ) (h₁ : (66777/16384:ℝ) ≤ x) (h₂ : x ≤ (66797/16384:ℝ)) : (60517089/400000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2379587697/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2417937217/10000000000:ℝ) := by nlinarith
  have hc1 : (19418200757/20000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (19418200757/20000000000:ℝ) ≤ taylorCos (2417937217/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (971821158983/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2379587697/10000000000:ℝ) + taylorErr ≤ (971821158983/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (58929851457/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (58929851457/250000000000:ℝ) ≤ taylorSin (2379587697/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (119722277681/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2417937217/10000000000:ℝ) + taylorErr ≤ (119722277681/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (19418200757/20000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (971821158983/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (58929851457/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (119722277681/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12804329384079/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (256163286721/20000000000:ℝ) := by nlinarith
  have hp1 : (21191146966429/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21197494090843/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (249758228587/50000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (5075624547371/1000000000000:ℝ) := by nlinarith
  have hN : (4023343412757/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (327098147318527/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4023343412757/1000000000000:ℝ) (327098147318527/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (60517089/400000000000:ℝ) ≤ ((4023343412757/1000000000000:ℝ)/(327098147318527/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1049 (x : ℝ) (h₁ : (66777/16384:ℝ) ≤ x) (h₂ : x ≤ (33401/8192:ℝ)) : (1512472933/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2379587697/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2427524597/10000000000:ℝ) := by nlinarith
  have hc1 : (485340013537/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (485340013537/500000000000:ℝ) ≤ taylorCos (2427524597/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (971821158983/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2379587697/10000000000:ℝ) + taylorErr ≤ (971821158983/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (58929851457/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (58929851457/250000000000:ℝ) ≤ taylorSin (2379587697/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (971821158983/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (58929851457/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (240375293523/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12804329384079/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12809123074043/1000000000000:ℝ) := by nlinarith
  have hp1 : (21191146966429/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10599540400441/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (249758228587/50000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (509573526993/100000000000:ℝ) := by nlinarith
  have hN : (4023343412757/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (163573633925981/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4023343412757/1000000000000:ℝ) (163573633925981/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1512472933/10000000000000:ℝ) ≤ ((4023343412757/1000000000000:ℝ)/(163573633925981/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1050 (x : ℝ) (h₁ : (33391/8192:ℝ) ≤ x) (h₂ : x ≤ (66797/16384:ℝ)) : (1528266033/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2389175077/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2417937217/10000000000:ℝ) := by nlinarith
  have hc1 : (19418200757/20000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (19418200757/20000000000:ℝ) ≤ taylorCos (2417937217/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (38863788769/40000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2389175077/10000000000:ℝ) + taylorErr ≤ (38863788769/40000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (236651019223/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (236651019223/1000000000000:ℝ) ≤ taylorSin (2389175077/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (119722277681/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2417937217/10000000000:ℝ) + taylorErr ≤ (119722277681/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (19418200757/20000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (38863788769/40000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (236651019223/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (119722277681/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1600661015259/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (256163286721/20000000000:ℝ) := by nlinarith
  have hp1 : (21192733676447/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21197494090843/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1253820506163/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (5075624547371/1000000000000:ℝ) := by nlinarith
  have hN : (4043687305427/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (327098147318527/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4043687305427/1000000000000:ℝ) (327098147318527/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1528266033/10000000000000:ℝ) ≤ ((4043687305427/1000000000000:ℝ)/(327098147318527/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1051 (x : ℝ) (h₁ : (33391/8192:ℝ) ≤ x) (h₂ : x ≤ (33401/8192:ℝ)) : (305561427/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2389175077/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2427524597/10000000000:ℝ) := by nlinarith
  have hc1 : (485340013537/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (485340013537/500000000000:ℝ) ≤ taylorCos (2427524597/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (38863788769/40000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2389175077/10000000000:ℝ) + taylorErr ≤ (38863788769/40000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (236651019223/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (236651019223/1000000000000:ℝ) ≤ taylorSin (2389175077/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (38863788769/40000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (236651019223/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (240375293523/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1600661015259/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12809123074043/1000000000000:ℝ) := by nlinarith
  have hp1 : (21192733676447/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10599540400441/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1253820506163/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (509573526993/100000000000:ℝ) := by nlinarith
  have hN : (4043687305427/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (163573633925981/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4043687305427/1000000000000:ℝ) (163573633925981/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (305561427/2000000000000:ℝ) ≤ ((4043687305427/1000000000000:ℝ)/(163573633925981/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1052 (x : ℝ) (h₁ : (33391/8192:ℝ) ≤ x) (h₂ : x ≤ (66807/16384:ℝ)) : (1527348409/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2389175077/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2437111977/10000000000:ℝ) := by nlinarith
  have hc1 : (970449124069/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (970449124069/1000000000000:ℝ) ≤ taylorCos (2437111977/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (38863788769/40000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2389175077/10000000000:ℝ) + taylorErr ≤ (38863788769/40000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (236651019223/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (236651019223/1000000000000:ℝ) ≤ taylorSin (2389175077/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (241305810737/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2437111977/10000000000:ℝ) + taylorErr ≤ (241305810737/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (970449124069/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (38863788769/40000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (236651019223/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (241305810737/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1600661015259/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2562016362407/200000000000:ℝ) := by nlinarith
  have hp1 : (21192733676447/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (530016687773/25000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1253820506163/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (5115844261889/1000000000000:ℝ) := by nlinarith
  have hN : (4043687305427/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (16359819603103/50000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4043687305427/1000000000000:ℝ) (16359819603103/50000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1527348409/10000000000000:ℝ) ≤ ((4043687305427/1000000000000:ℝ)/(16359819603103/50000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1053 (x : ℝ) (h₁ : (33391/8192:ℝ) ≤ x) (h₂ : x ≤ (16703/4096:ℝ)) : (11928827/78125000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2389175077/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2446699357/10000000000:ℝ) := by nlinarith
  have hc1 : (121277166131/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (121277166131/125000000000:ℝ) ≤ taylorCos (2446699357/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (38863788769/40000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2389175077/10000000000:ℝ) + taylorErr ≤ (38863788769/40000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (236651019223/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (236651019223/1000000000000:ℝ) ≤ taylorSin (2389175077/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (38863788769/40000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (236651019223/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (242236106147/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1600661015259/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12811040550027/1000000000000:ℝ) := by nlinarith
  have hp1 : (21192733676447/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10601127110479/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1253820506163/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (641993938003/125000000000:ℝ) := by nlinarith
  have hN : (4043687305427/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (327245519948873/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4043687305427/1000000000000:ℝ) (327245519948873/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (11928827/78125000000:ℝ) ≤ ((4043687305427/1000000000000:ℝ)/(327245519948873/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1054 (x : ℝ) (h₁ : (33391/8192:ℝ) ≤ x) (h₂ : x ≤ (33411/8192:ℝ)) : (305194653/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2389175077/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2465874117/10000000000:ℝ) := by nlinarith
  have hc1 : (242437765953/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (242437765953/250000000000:ℝ) ≤ taylorCos (2465874117/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (38863788769/40000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2389175077/10000000000:ℝ) + taylorErr ≤ (38863788769/40000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (236651019223/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (236651019223/1000000000000:ℝ) ≤ taylorSin (2389175077/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (122048014069/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2465874117/10000000000:ℝ) + taylorErr ≤ (122048014069/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (242437765953/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (38863788769/40000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (236651019223/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (122048014069/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1600661015259/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3203239506503/250000000000:ℝ) := by nlinarith
  have hp1 : (21192733676447/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5301356910259/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1253820506163/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1035232132429/200000000000:ℝ) := by nlinarith
  have hN : (4043687305427/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (327343786752691/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4043687305427/1000000000000:ℝ) (327343786752691/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (305194653/2000000000000:ℝ) ≤ ((4043687305427/1000000000000:ℝ)/(327343786752691/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1055 (x : ℝ) (h₁ : (33391/8192:ℝ) ≤ x) (h₂ : x ≤ (4177/1024:ℝ)) : (1525057363/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2389175077/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2485048877/10000000000:ℝ) := by nlinarith
  have hc1 : (969281233079/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (969281233079/1000000000000:ℝ) ≤ taylorCos (2485048877/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (38863788769/40000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2389175077/10000000000:ℝ) + taylorErr ≤ (38863788769/40000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (236651019223/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (236651019223/1000000000000:ℝ) ≤ taylorSin (2389175077/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (38863788769/40000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (236651019223/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (245955052659/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1600661015259/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12814875501997/1000000000000:ℝ) := by nlinarith
  have hp1 : (21192733676447/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21208601061113/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1253820506163/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (521636259081/100000000000:ℝ) := by nlinarith
  have hN : (4043687305427/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (163721034131683/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4043687305427/1000000000000:ℝ) (163721034131683/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1525057363/10000000000000:ℝ) ≤ ((4043687305427/1000000000000:ℝ)/(163721034131683/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1056 (x : ℝ) (h₁ : (66787/16384:ℝ) ≤ x) (h₂ : x ≤ (33401/8192:ℝ)) : (15432181/100000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2398762457/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2427524597/10000000000:ℝ) := by nlinarith
  have hc1 : (485340013537/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (485340013537/500000000000:ℝ) ≤ taylorCos (2427524597/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (485683693199/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2398762457/10000000000:ℝ) + taylorErr ≤ (485683693199/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (118791207547/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (118791207547/500000000000:ℝ) ≤ taylorSin (2398762457/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (485683693199/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (118791207547/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (240375293523/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (400195214377/31250000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12809123074043/1000000000000:ℝ) := by nlinarith
  have hp1 : (662322512077/31250000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10599540400441/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1258849455923/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (509573526993/100000000000:ℝ) := by nlinarith
  have hN : (2032015218647/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (163573633925981/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2032015218647/500000000000:ℝ) (163573633925981/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (15432181/100000000000:ℝ) ≤ ((2032015218647/500000000000:ℝ)/(163573633925981/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1057 (x : ℝ) (h₁ : (66787/16384:ℝ) ≤ x) (h₂ : x ≤ (66807/16384:ℝ)) : (1542754747/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2398762457/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2437111977/10000000000:ℝ) := by nlinarith
  have hc1 : (970449124069/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (970449124069/1000000000000:ℝ) ≤ taylorCos (2437111977/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (485683693199/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2398762457/10000000000:ℝ) + taylorErr ≤ (485683693199/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (118791207547/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (118791207547/500000000000:ℝ) ≤ taylorSin (2398762457/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (241305810737/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2437111977/10000000000:ℝ) + taylorErr ≤ (241305810737/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (970449124069/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (485683693199/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (118791207547/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (241305810737/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (400195214377/31250000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2562016362407/200000000000:ℝ) := by nlinarith
  have hp1 : (662322512077/31250000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (530016687773/25000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1258849455923/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (5115844261889/1000000000000:ℝ) := by nlinarith
  have hN : (2032015218647/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (16359819603103/50000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2032015218647/500000000000:ℝ) (16359819603103/50000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1542754747/10000000000000:ℝ) ≤ ((2032015218647/500000000000:ℝ)/(16359819603103/50000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1058 (x : ℝ) (h₁ : (66787/16384:ℝ) ≤ x) (h₂ : x ≤ (16703/4096:ℝ)) : (96393223/625000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2398762457/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2446699357/10000000000:ℝ) := by nlinarith
  have hc1 : (121277166131/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (121277166131/125000000000:ℝ) ≤ taylorCos (2446699357/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (485683693199/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2398762457/10000000000:ℝ) + taylorErr ≤ (485683693199/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (118791207547/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (118791207547/500000000000:ℝ) ≤ taylorSin (2398762457/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (485683693199/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (118791207547/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (242236106147/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (400195214377/31250000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12811040550027/1000000000000:ℝ) := by nlinarith
  have hp1 : (662322512077/31250000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10601127110479/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1258849455923/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (641993938003/125000000000:ℝ) := by nlinarith
  have hN : (2032015218647/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (327245519948873/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2032015218647/500000000000:ℝ) (327245519948873/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (96393223/625000000000:ℝ) ≤ ((2032015218647/500000000000:ℝ)/(327245519948873/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1059 (x : ℝ) (h₁ : (8349/2048:ℝ) ≤ x) (h₂ : x ≤ (66807/16384:ℝ)) : (7791189/50000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (602087459/2500000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2437111977/10000000000:ℝ) := by nlinarith
  have hc1 : (970449124069/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (970449124069/1000000000000:ℝ) ≤ taylorCos (2437111977/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (194227832147/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (602087459/2500000000:ℝ) + taylorErr ≤ (194227832147/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (238513592487/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (238513592487/1000000000000:ℝ) ≤ taylorSin (602087459/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (241305810737/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2437111977/10000000000:ℝ) + taylorErr ≤ (241305810737/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (970449124069/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (194227832147/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (238513592487/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (241305810737/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12807205598057/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2562016362407/200000000000:ℝ) := by nlinarith
  have hp1 : (10597953548241/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (530016687773/25000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2527755973801/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (5115844261889/1000000000000:ℝ) := by nlinarith
  have hN : (4084372786867/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (16359819603103/50000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4084372786867/1000000000000:ℝ) (16359819603103/50000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (7791189/50000000000:ℝ) ≤ ((4084372786867/1000000000000:ℝ)/(16359819603103/50000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1060 (x : ℝ) (h₁ : (8349/2048:ℝ) ≤ x) (h₂ : x ≤ (16703/4096:ℝ)) : (1557769973/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (602087459/2500000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2446699357/10000000000:ℝ) := by nlinarith
  have hc1 : (121277166131/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (121277166131/125000000000:ℝ) ≤ taylorCos (2446699357/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (194227832147/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (602087459/2500000000:ℝ) + taylorErr ≤ (194227832147/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (238513592487/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (238513592487/1000000000000:ℝ) ≤ taylorSin (602087459/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (194227832147/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (238513592487/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (242236106147/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12807205598057/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12811040550027/1000000000000:ℝ) := by nlinarith
  have hp1 : (10597953548241/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10601127110479/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2527755973801/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (641993938003/125000000000:ℝ) := by nlinarith
  have hN : (4084372786867/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (327245519948873/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4084372786867/1000000000000:ℝ) (327245519948873/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1557769973/10000000000000:ℝ) ≤ ((4084372786867/1000000000000:ℝ)/(327245519948873/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1061 (x : ℝ) (h₁ : (8349/2048:ℝ) ≤ x) (h₂ : x ≤ (66817/16384:ℝ)) : (778651161/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (602087459/2500000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2456286737/10000000000:ℝ) := by nlinarith
  have hc1 : (60624040139/62500000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (60624040139/62500000000:ℝ) ≤ taylorCos (2456286737/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (194227832147/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (602087459/2500000000:ℝ) + taylorErr ≤ (194227832147/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (238513592487/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (238513592487/1000000000000:ℝ) ≤ taylorSin (602087459/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (243166178899/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2456286737/10000000000:ℝ) + taylorErr ≤ (243166178899/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (60624040139/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (194227832147/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (238513592487/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (243166178899/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12807205598057/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (640599964401/50000000000:ℝ) := by nlinarith
  have hp1 : (10597953548241/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10601920465499/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2527755973801/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (5156056977173/1000000000000:ℝ) := by nlinarith
  have hN : (4084372786867/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (6545893030249/20000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4084372786867/1000000000000:ℝ) (6545893030249/20000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (778651161/5000000000000:ℝ) ≤ ((4084372786867/1000000000000:ℝ)/(6545893030249/20000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1062 (x : ℝ) (h₁ : (8349/2048:ℝ) ≤ x) (h₂ : x ≤ (33411/8192:ℝ)) : (778417423/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (602087459/2500000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2465874117/10000000000:ℝ) := by nlinarith
  have hc1 : (242437765953/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (242437765953/250000000000:ℝ) ≤ taylorCos (2465874117/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (194227832147/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (602087459/2500000000:ℝ) + taylorErr ≤ (194227832147/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (238513592487/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (238513592487/1000000000000:ℝ) ≤ taylorSin (602087459/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (122048014069/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2465874117/10000000000:ℝ) + taylorErr ≤ (122048014069/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (242437765953/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (194227832147/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (238513592487/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (122048014069/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12807205598057/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3203239506503/250000000000:ℝ) := by nlinarith
  have hp1 : (10597953548241/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5301356910259/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2527755973801/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1035232132429/200000000000:ℝ) := by nlinarith
  have hN : (4084372786867/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (327343786752691/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4084372786867/1000000000000:ℝ) (327343786752691/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (778417423/5000000000000:ℝ) ≤ ((4084372786867/1000000000000:ℝ)/(327343786752691/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1063 (x : ℝ) (h₁ : (8349/2048:ℝ) ≤ x) (h₂ : x ≤ (4177/1024:ℝ)) : (77795021/500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (602087459/2500000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2485048877/10000000000:ℝ) := by nlinarith
  have hc1 : (969281233079/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (969281233079/1000000000000:ℝ) ≤ taylorCos (2485048877/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (194227832147/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (602087459/2500000000:ℝ) + taylorErr ≤ (194227832147/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (238513592487/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (238513592487/1000000000000:ℝ) ≤ taylorSin (602087459/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (194227832147/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (238513592487/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (245955052659/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12807205598057/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12814875501997/1000000000000:ℝ) := by nlinarith
  have hp1 : (10597953548241/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21208601061113/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2527755973801/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (521636259081/100000000000:ℝ) := by nlinarith
  have hN : (4084372786867/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (163721034131683/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4084372786867/1000000000000:ℝ) (163721034131683/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (77795021/500000000000:ℝ) ≤ ((4084372786867/1000000000000:ℝ)/(163721034131683/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1064 (x : ℝ) (h₁ : (8349/2048:ℝ) ≤ x) (h₂ : x ≤ (33421/8192:ℝ)) : (194370837/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (602087459/2500000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2504223637/10000000000:ℝ) := by nlinarith
  have hc1 : (968807838577/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (968807838577/1000000000000:ℝ) ≤ taylorCos (2504223637/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (194227832147/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (602087459/2500000000:ℝ) + taylorErr ≤ (194227832147/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (238513592487/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (238513592487/1000000000000:ℝ) ≤ taylorSin (602087459/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (247813172873/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2504223637/10000000000:ℝ) + taylorErr ≤ (247813172873/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (968807838577/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (194227832147/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (238513592487/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (247813172873/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12807205598057/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6408396488991/500000000000:ℝ) := by nlinarith
  have hp1 : (10597953548241/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21211774481191/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2527755973801/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (5256557136451/1000000000000:ℝ) := by nlinarith
  have hN : (4084372786867/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (163770182240449/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4084372786867/1000000000000:ℝ) (163770182240449/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (194370837/1250000000000:ℝ) ≤ ((4084372786867/1000000000000:ℝ)/(163770182240449/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1065 (x : ℝ) (h₁ : (8349/2048:ℝ) ≤ x) (h₂ : x ≤ (16713/4096:ℝ)) : (1554033673/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (602087459/2500000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2523398397/10000000000:ℝ) := by nlinarith
  have hc1 : (968330882047/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (968330882047/1000000000000:ℝ) ≤ taylorCos (2523398397/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (194227832147/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (602087459/2500000000:ℝ) + taylorErr ≤ (194227832147/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (238513592487/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (238513592487/1000000000000:ℝ) ≤ taylorSin (602087459/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (194227832147/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (238513592487/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (249670381949/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12807205598057/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12818710453967/1000000000000:ℝ) := by nlinarith
  have hp1 : (10597953548241/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21214947901269/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2527755973801/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (2648372072769/500000000000:ℝ) := by nlinarith
  have hN : (4084372786867/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (163819337702643/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4084372786867/1000000000000:ℝ) (163819337702643/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1554033673/10000000000000:ℝ) ≤ ((4084372786867/1000000000000:ℝ)/(163819337702643/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1066 (x : ℝ) (h₁ : (8349/2048:ℝ) ≤ x) (h₂ : x ≤ (8359/2048:ℝ)) : (62086789/400000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (602087459/2500000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (640436979/2500000000:ℝ) := by nlinarith
  have hc1 : (483683144977/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (483683144977/500000000000:ℝ) ≤ taylorCos (640436979/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (194227832147/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (602087459/2500000000:ℝ) + taylorErr ≤ (194227832147/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (238513592487/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (238513592487/1000000000000:ℝ) ≤ taylorSin (602087459/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (194227832147/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (238513592487/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (3167275491/12500000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12807205598057/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12822545405937/1000000000000:ℝ) := by nlinarith
  have hp1 : (10597953548241/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1326330921339/62500000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2527755973801/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (336068433609/62500000000:ℝ) := by nlinarith
  have hN : (4084372786867/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (327835341374633/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4084372786867/1000000000000:ℝ) (327835341374633/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (62086789/400000000000:ℝ) ≤ ((4084372786867/1000000000000:ℝ)/(327835341374633/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1067 (x : ℝ) (h₁ : (8349/2048:ℝ) ≤ x) (h₂ : x ≤ (16723/4096:ℝ)) : (775154287/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (602087459/2500000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (650024359/2500000000:ℝ) := by nlinarith
  have hc1 : (120798433867/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (120798433867/125000000000:ℝ) ≤ taylorCos (650024359/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (194227832147/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (602087459/2500000000:ℝ) + taylorErr ≤ (194227832147/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (238513592487/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (238513592487/1000000000000:ℝ) ≤ taylorSin (602087459/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (257089970259/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (650024359/2500000000:ℝ) + taylorErr ≤ (257089970259/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (120798433867/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (194227832147/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (238513592487/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (257089970259/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12807205598057/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6413190178953/500000000000:ℝ) := by nlinarith
  have hp1 : (10597953548241/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21227641581577/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2527755973801/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (5457413742877/1000000000000:ℝ) := by nlinarith
  have hN : (4084372786867/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (164016033085677/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4084372786867/1000000000000:ℝ) (164016033085677/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (775154287/5000000000000:ℝ) ≤ ((4084372786867/1000000000000:ℝ)/(164016033085677/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1068 (x : ℝ) (h₁ : (8349/2048:ℝ) ≤ x) (h₂ : x ≤ (2091/512:ℝ)) : (1548450213/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (602087459/2500000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (659611739/2500000000:ℝ) := by nlinarith
  have hc1 : (482697219707/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (482697219707/500000000000:ℝ) ≤ taylorCos (659611739/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (194227832147/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (602087459/2500000000:ℝ) + taylorErr ≤ (194227832147/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (238513592487/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (238513592487/1000000000000:ℝ) ≤ taylorSin (602087459/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (194227832147/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (238513592487/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (130397060129/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12807205598057/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3207553827469/250000000000:ℝ) := by nlinarith
  have hp1 : (10597953548241/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21233988421733/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2527755973801/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1107539866003/200000000000:ℝ) := by nlinarith
  have hN : (4084372786867/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (164114424897777/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4084372786867/1000000000000:ℝ) (164114424897777/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1548450213/10000000000000:ℝ) ≤ ((4084372786867/1000000000000:ℝ)/(164114424897777/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1069 (x : ℝ) (h₁ : (8349/2048:ℝ) ≤ x) (h₂ : x ≤ (8369/2048:ℝ)) : (1544741841/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (602087459/2500000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (543029199/2000000000:ℝ) := by nlinarith
  have hc1 : (963365797507/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (963365797507/1000000000000:ℝ) ≤ taylorCos (543029199/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (194227832147/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (602087459/2500000000:ℝ) + taylorErr ≤ (194227832147/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (238513592487/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (238513592487/1000000000000:ℝ) ≤ taylorSin (602087459/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (194227832147/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (238513592487/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (33523857421/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12807205598057/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2567577042763/200000000000:ℝ) := by nlinarith
  have hp1 : (10597953548241/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21246682102041/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2527755973801/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (2849082965833/500000000000:ℝ) := by nlinarith
  have hN : (4084372786867/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (16431129676309/50000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4084372786867/1000000000000:ℝ) (16431129676309/50000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1544741841/10000000000000:ℝ) ≤ ((4084372786867/1000000000000:ℝ)/(16431129676309/50000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1070 (x : ℝ) (h₁ : (8349/2048:ℝ) ≤ x) (h₂ : x ≤ (4187/1024:ℝ)) : (1541044571/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (602087459/2500000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1395922517/5000000000:ℝ) := by nlinarith
  have hc1 : (240320120887/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (240320120887/250000000000:ℝ) ≤ taylorCos (1395922517/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (194227832147/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (602087459/2500000000:ℝ) + taylorErr ≤ (194227832147/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (238513592487/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (238513592487/1000000000000:ℝ) ≤ taylorSin (602087459/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (194227832147/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (238513592487/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (137785910789/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12807205598057/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2569111023551/200000000000:ℝ) := by nlinarith
  have hp1 : (10597953548241/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1328710986397/62500000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2527755973801/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (2929242454977/500000000000:ℝ) := by nlinarith
  have hN : (4084372786867/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (82254143141641/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4084372786867/1000000000000:ℝ) (82254143141641/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1541044571/10000000000000:ℝ) ≤ ((4084372786867/1000000000000:ℝ)/(82254143141641/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1071 (x : ℝ) (h₁ : (66797/16384:ℝ) ≤ x) (h₂ : x ≤ (16703/4096:ℝ)) : (31466501/200000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (37780269/156250000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2446699357/10000000000:ℝ) := by nlinarith
  have hc1 : (121277166131/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (121277166131/125000000000:ℝ) ≤ taylorCos (2446699357/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (485455021199/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (37780269/156250000:ℝ) + taylorErr ≤ (485455021199/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (239444550741/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (239444550741/1000000000000:ℝ) ≤ taylorSin (37780269/156250000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (485455021199/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (239444550741/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (242236106147/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12808164336049/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12811040550027/1000000000000:ℝ) := by nlinarith
  have hp1 : (21197493806499/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10601127110479/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1268906095333/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (641993938003/125000000000:ℝ) := by nlinarith
  have hN : (2052357169467/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (327245519948873/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2052357169467/500000000000:ℝ) (327245519948873/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (31466501/200000000000:ℝ) ≤ ((2052357169467/500000000000:ℝ)/(327245519948873/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1072 (x : ℝ) (h₁ : (66797/16384:ℝ) ≤ x) (h₂ : x ≤ (66817/16384:ℝ)) : (1572852729/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (37780269/156250000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2456286737/10000000000:ℝ) := by nlinarith
  have hc1 : (60624040139/62500000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (60624040139/62500000000:ℝ) ≤ taylorCos (2456286737/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (485455021199/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (37780269/156250000:ℝ) + taylorErr ≤ (485455021199/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (239444550741/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (239444550741/1000000000000:ℝ) ≤ taylorSin (37780269/156250000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (243166178899/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2456286737/10000000000:ℝ) + taylorErr ≤ (243166178899/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (60624040139/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (485455021199/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (239444550741/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (243166178899/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12808164336049/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (640599964401/50000000000:ℝ) := by nlinarith
  have hp1 : (21197493806499/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10601920465499/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1268906095333/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (5156056977173/1000000000000:ℝ) := by nlinarith
  have hN : (2052357169467/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (6545893030249/20000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2052357169467/500000000000:ℝ) (6545893030249/20000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1572852729/10000000000000:ℝ) ≤ ((2052357169467/500000000000:ℝ)/(6545893030249/20000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1073 (x : ℝ) (h₁ : (66797/16384:ℝ) ≤ x) (h₂ : x ≤ (33411/8192:ℝ)) : (314476117/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (37780269/156250000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2465874117/10000000000:ℝ) := by nlinarith
  have hc1 : (242437765953/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (242437765953/250000000000:ℝ) ≤ taylorCos (2465874117/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (485455021199/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (37780269/156250000:ℝ) + taylorErr ≤ (485455021199/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (239444550741/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (239444550741/1000000000000:ℝ) ≤ taylorSin (37780269/156250000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (122048014069/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2465874117/10000000000:ℝ) + taylorErr ≤ (122048014069/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (242437765953/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (485455021199/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (239444550741/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (122048014069/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12808164336049/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3203239506503/250000000000:ℝ) := by nlinarith
  have hp1 : (21197493806499/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5301356910259/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1268906095333/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1035232132429/200000000000:ℝ) := by nlinarith
  have hN : (2052357169467/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (327343786752691/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2052357169467/500000000000:ℝ) (327343786752691/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (314476117/2000000000000:ℝ) ≤ ((2052357169467/500000000000:ℝ)/(327343786752691/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1074 (x : ℝ) (h₁ : (33401/8192:ℝ) ≤ x) (h₂ : x ≤ (33411/8192:ℝ)) : (397000731/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (606881149/2500000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2465874117/10000000000:ℝ) := by nlinarith
  have hc1 : (242437765953/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (242437765953/250000000000:ℝ) ≤ taylorCos (2465874117/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (485340015811/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (606881149/2500000000:ℝ) + taylorErr ≤ (485340015811/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (120187644451/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (120187644451/500000000000:ℝ) ≤ taylorSin (606881149/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (122048014069/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2465874117/10000000000:ℝ) + taylorErr ≤ (122048014069/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (242437765953/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (485340015811/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (120187644451/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (122048014069/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6404561537021/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3203239506503/250000000000:ℝ) := by nlinarith
  have hp1 : (21199080516517/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5301356910259/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2547867551807/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1035232132429/200000000000:ℝ) := by nlinarith
  have hN : (515631883999/125000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (327343786752691/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (515631883999/125000000000:ℝ) (327343786752691/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (397000731/2500000000000:ℝ) ≤ ((515631883999/125000000000:ℝ)/(327343786752691/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1075 (x : ℝ) (h₁ : (33401/8192:ℝ) ≤ x) (h₂ : x ≤ (66827/16384:ℝ)) : (396881567/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (606881149/2500000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2475461497/10000000000:ℝ) := by nlinarith
  have hc1 : (38780663761/40000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (38780663761/40000000000:ℝ) ≤ taylorCos (2475461497/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (485340015811/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (606881149/2500000000:ℝ) + taylorErr ≤ (485340015811/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (120187644451/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (120187644451/500000000000:ℝ) ≤ taylorSin (606881149/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (24502565301/100000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2475461497/10000000000:ℝ) + taylorErr ≤ (24502565301/100000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (38780663761/40000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (485340015811/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (120187644451/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (24502565301/100000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6404561537021/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2562783352801/200000000000:ℝ) := by nlinarith
  have hp1 : (21199080516517/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (848280574043/40000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2547867551807/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1039252507953/200000000000:ℝ) := by nlinarith
  have hN : (515631883999/125000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (327392925669697/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (515631883999/125000000000:ℝ) (327392925669697/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (396881567/2500000000000:ℝ) ≤ ((515631883999/125000000000:ℝ)/(327392925669697/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1076 (x : ℝ) (h₁ : (33401/8192:ℝ) ≤ x) (h₂ : x ≤ (4177/1024:ℝ)) : (1587049791/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (606881149/2500000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2485048877/10000000000:ℝ) := by nlinarith
  have hc1 : (969281233079/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (969281233079/1000000000000:ℝ) ≤ taylorCos (2485048877/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (485340015811/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (606881149/2500000000:ℝ) + taylorErr ≤ (485340015811/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (120187644451/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (120187644451/500000000000:ℝ) ≤ taylorSin (606881149/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (485340015811/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (120187644451/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (245955052659/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6404561537021/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12814875501997/1000000000000:ℝ) := by nlinarith
  have hp1 : (21199080516517/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21208601061113/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2547867551807/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (521636259081/100000000000:ℝ) := by nlinarith
  have hN : (515631883999/125000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (163721034131683/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (515631883999/125000000000:ℝ) (163721034131683/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1587049791/10000000000000:ℝ) ≤ ((515631883999/125000000000:ℝ)/(163721034131683/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1077 (x : ℝ) (h₁ : (33401/8192:ℝ) ≤ x) (h₂ : x ≤ (33421/8192:ℝ)) : (793048687/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (606881149/2500000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2504223637/10000000000:ℝ) := by nlinarith
  have hc1 : (968807838577/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (968807838577/1000000000000:ℝ) ≤ taylorCos (2504223637/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (485340015811/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (606881149/2500000000:ℝ) + taylorErr ≤ (485340015811/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (120187644451/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (120187644451/500000000000:ℝ) ≤ taylorSin (606881149/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (247813172873/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2504223637/10000000000:ℝ) + taylorErr ≤ (247813172873/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (968807838577/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (485340015811/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (120187644451/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (247813172873/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6404561537021/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6408396488991/500000000000:ℝ) := by nlinarith
  have hp1 : (21199080516517/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21211774481191/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2547867551807/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (5256557136451/1000000000000:ℝ) := by nlinarith
  have hN : (515631883999/125000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (163770182240449/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (515631883999/125000000000:ℝ) (163770182240449/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (793048687/5000000000000:ℝ) ≤ ((515631883999/125000000000:ℝ)/(163770182240449/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1078 (x : ℝ) (h₁ : (33401/8192:ℝ) ≤ x) (h₂ : x ≤ (16713/4096:ℝ)) : (1585145671/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (606881149/2500000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2523398397/10000000000:ℝ) := by nlinarith
  have hc1 : (968330882047/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (968330882047/1000000000000:ℝ) ≤ taylorCos (2523398397/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (485340015811/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (606881149/2500000000:ℝ) + taylorErr ≤ (485340015811/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (120187644451/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (120187644451/500000000000:ℝ) ≤ taylorSin (606881149/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (485340015811/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (120187644451/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (249670381949/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6404561537021/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12818710453967/1000000000000:ℝ) := by nlinarith
  have hp1 : (21199080516517/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21214947901269/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2547867551807/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (2648372072769/500000000000:ℝ) := by nlinarith
  have hN : (515631883999/125000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (163819337702643/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (515631883999/125000000000:ℝ) (163819337702643/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1585145671/10000000000000:ℝ) ≤ ((515631883999/125000000000:ℝ)/(163819337702643/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1079 (x : ℝ) (h₁ : (66807/16384:ℝ) ≤ x) (h₂ : x ≤ (66827/16384:ℝ)) : (1603220471/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (304638997/1250000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2475461497/10000000000:ℝ) := by nlinarith
  have hc1 : (38780663761/40000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (38780663761/40000000000:ℝ) ≤ taylorCos (2475461497/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (970449128617/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (304638997/1250000000:ℝ) + taylorErr ≤ (970449128617/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (48261161223/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (48261161223/200000000000:ℝ) ≤ taylorSin (304638997/1250000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (24502565301/100000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2475461497/10000000000:ℝ) + taylorErr ≤ (24502565301/100000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (38780663761/40000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (970449128617/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (48261161223/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (24502565301/100000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6405040906017/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2562783352801/200000000000:ℝ) := by nlinarith
  have hp1 : (10600333613267/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (848280574043/40000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2557922047637/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1039252507953/200000000000:ℝ) := by nlinarith
  have hN : (4145394966657/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (327392925669697/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4145394966657/1000000000000:ℝ) (327392925669697/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1603220471/10000000000000:ℝ) ≤ ((4145394966657/1000000000000:ℝ)/(327392925669697/1000000000000:ℝ))^2 := by norm_num
  linarith

end Zeta23Ext.Bridge.FourPoint
