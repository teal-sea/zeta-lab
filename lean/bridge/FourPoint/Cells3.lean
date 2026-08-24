import FourPoint.Base

noncomputable section
open Real
namespace Zeta23Ext.Bridge.FourPoint


theorem wc_180 (x : ℝ) (h₁ : (141/64:ℝ) ≤ x) (h₂ : x ≤ (71/32:ℝ)) : (39186989529/10000000000000:ℝ) ≤ wfun x := by
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

theorem wc_181 (x : ℝ) (h₁ : (71/32:ℝ) ≤ x) (h₂ : x ≤ (9/4:ℝ)) : (21886858333/5000000000000:ℝ) ≤ wfun x := by
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

theorem wc_182 (x : ℝ) (h₁ : (9/4:ℝ) ≤ x) (h₂ : x ≤ (73/32:ℝ)) : (27652304943/5000000000000:ℝ) ≤ wfun x := by
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

theorem wc_183 (x : ℝ) (h₁ : (9/4:ℝ) ≤ x) (h₂ : x ≤ (5/2:ℝ)) : (38217750111/10000000000000:ℝ) ≤ wfun x := by
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

theorem wc_184 (x : ℝ) (h₁ : (5/2:ℝ) ≤ x) (h₂ : x ≤ (11/4:ℝ)) : (38423148027/10000000000000:ℝ) ≤ wfun x := by
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

theorem wc_185 (x : ℝ) (h₁ : (11/4:ℝ) ≤ x) (h₂ : x ≤ (89/32:ℝ)) : (41549598057/10000000000000:ℝ) ≤ wfun x := by
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

theorem wc_186 (x : ℝ) (h₁ : (89/32:ℝ) ≤ x) (h₂ : x ≤ (179/64:ℝ)) : (37442452611/10000000000000:ℝ) ≤ wfun x := by
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

theorem wc_187 (x : ℝ) (h₁ : (179/64:ℝ) ≤ x) (h₂ : x ≤ (747/256:ℝ)) : (1457053011/2000000000000:ℝ) ≤ wfun x := by
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

theorem wc_188 (x : ℝ) (h₁ : (23/8:ℝ) ≤ x) (h₂ : x ≤ (383/128:ℝ)) : (269743281/5000000000000:ℝ) ≤ wfun x := by
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

theorem wc_189 (x : ℝ) (h₁ : (373/128:ℝ) ≤ x) (h₂ : x ≤ (383/128:ℝ)) : (288828359/5000000000000:ℝ) ≤ wfun x := by
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

theorem wc_190 (x : ℝ) (h₁ : (747/256:ℝ) ≤ x) (h₂ : x ≤ (6007/2048:ℝ)) : (2995265257/5000000000000:ℝ) ≤ wfun x := by
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

theorem wc_191 (x : ℝ) (h₁ : (747/256:ℝ) ≤ x) (h₂ : x ≤ (3019/1024:ℝ)) : (100676353/250000000000:ℝ) ≤ wfun x := by
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

theorem wc_192 (x : ℝ) (h₁ : (747/256:ℝ) ≤ x) (h₂ : x ≤ (1525/512:ℝ)) : (261299809/2000000000000:ℝ) ≤ wfun x := by
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

theorem wc_193 (x : ℝ) (h₁ : (6007/2048:ℝ) ≤ x) (h₂ : x ≤ (3019/1024:ℝ)) : (816631931/2000000000000:ℝ) ≤ wfun x := by
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

theorem wc_194 (x : ℝ) (h₁ : (3019/1024:ℝ) ≤ x) (h₂ : x ≤ (12107/4096:ℝ)) : (3285883949/10000000000000:ℝ) ≤ wfun x := by
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

theorem wc_195 (x : ℝ) (h₁ : (3019/1024:ℝ) ≤ x) (h₂ : x ≤ (6069/2048:ℝ)) : (2539642107/10000000000000:ℝ) ≤ wfun x := by
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

theorem wc_196 (x : ℝ) (h₁ : (3019/1024:ℝ) ≤ x) (h₂ : x ≤ (1525/512:ℝ)) : (67339097/500000000000:ℝ) ≤ wfun x := by
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

theorem wc_197 (x : ℝ) (h₁ : (189/64:ℝ) ≤ x) (h₂ : x ≤ (383/128:ℝ)) : (15105971/250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/5000000000:ℝ) ≤ Real.pi * ((3:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((3:ℝ) - x) ≤ (1472621557/10000000000:ℝ) := by nlinarith
  have hc1 : (989176507693/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (989176507693/1000000000000:ℝ) ≤ taylorCos (1472621557/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((3:ℝ) - x)) ≤ (999698820959/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/5000000000:ℝ) + taylorErr ≤ (999698820959/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (4908245251/200000000000:ℝ) ≤ Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (4908245251/200000000000:ℝ) ≤ taylorSin (122718463/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-999698820959/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-989176507693/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (4908245251/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (7336523839/50000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (2319378951283/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2350058567041/250000000000:ℝ) := by nlinarith
  have hp1 : (15354275496409/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (622294983493/40000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (188406374469/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (570685247661/250000000000:ℝ) := by nlinarith
  have hN : (1365989256631/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (17572880859273/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1365989256631/1000000000000:ℝ) (17572880859273/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (15105971/250000000000:ℝ) ≤ ((1365989256631/1000000000000:ℝ)/(17572880859273/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_198 (x : ℝ) (h₁ : (189/64:ℝ) ≤ x) (h₂ : x ≤ (3:ℝ)) : (156774751/5000000000000:ℝ) ≤ wfun x := by
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

theorem wc_199 (x : ℝ) (h₁ : (12107/4096:ℝ) ≤ x) (h₂ : x ≤ (24245/8192:ℝ)) : (2917054281/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1269369101/10000000000:ℝ) ≤ Real.pi * ((3:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((3:ℝ) - x) ≤ (694126307/5000000000:ℝ) := by nlinarith
  have hc1 : (495189618671/500000000000:ℝ) ≤ Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (495189618671/500000000000:ℝ) ≤ taylorCos (694126307/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((3:ℝ) - x)) ≤ (495977162359/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1269369101/10000000000:ℝ) + taylorErr ≤ (495977162359/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (63298146869/500000000000:ℝ) ≤ Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (63298146869/500000000000:ℝ) ≤ taylorSin (1269369101/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((3:ℝ) - x)) ≤ (27675955187/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (694126307/5000000000:ℝ) + taylorErr ≤ (27675955187/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h, cos_flip (3:ℝ) x, sin_flip (3:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h, cos_flip (3:ℝ) x, sin_flip (3:ℝ) x]; ring
  have hcxl : (-495977162359/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-495189618671/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (63298146869/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (27675955187/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1857190539893/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2324460262643/250000000000:ℝ) := by nlinarith
  have hp1 : (7684119272281/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1923489244399/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1945562041023/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (2129376085227/1000000000000:ℝ) := by nlinarith
  have hN : (587188255673/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (42974924100851/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (587188255673/200000000000:ℝ) (42974924100851/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2917054281/10000000000000:ℝ) ≤ ((587188255673/200000000000:ℝ)/(42974924100851/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_200 (x : ℝ) (h₁ : (12107/4096:ℝ) ≤ x) (h₂ : x ≤ (6069/2048:ℝ)) : (319327517/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (115048559/1000000000:ℝ) ≤ Real.pi * ((3:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((3:ℝ) - x) ≤ (694126307/5000000000:ℝ) := by nlinarith
  have hc1 : (495189618671/500000000000:ℝ) ≤ Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (495189618671/500000000000:ℝ) ≤ taylorCos (694126307/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((3:ℝ) - x)) ≤ (993389213421/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (115048559/1000000000:ℝ) + taylorErr ≤ (993389213421/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (57397462127/500000000000:ℝ) ≤ Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (57397462127/500000000000:ℝ) ≤ taylorSin (115048559/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((3:ℝ) - x)) ≤ (27675955187/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (694126307/5000000000:ℝ) + taylorErr ≤ (27675955187/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (-495189618671/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (57397462127/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (27675955187/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1857190539893/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (4654864700839/500000000000:ℝ) := by nlinarith
  have hp1 : (7684119272281/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15407589159671/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (44104894491/25000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1066049367807/500000000000:ℝ) := by nlinarith
  have hN : (1377287508491/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (21542765383117/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1377287508491/500000000000:ℝ) (21542765383117/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (319327517/1250000000000:ℝ) ≤ ((1377287508491/500000000000:ℝ)/(21542765383117/125000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_201 (x : ℝ) (h₁ : (24245/8192:ℝ) ≤ x) (h₂ : x ≤ (6069/2048:ℝ)) : (2561735901/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (115048559/1000000000:ℝ) ≤ Real.pi * ((3:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((3:ℝ) - x) ≤ (634684551/5000000000:ℝ) := by nlinarith
  have hc1 : (991954320181/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (991954320181/1000000000000:ℝ) ≤ taylorCos (634684551/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((3:ℝ) - x)) ≤ (993389213421/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (115048559/1000000000:ℝ) + taylorErr ≤ (993389213421/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (57397462127/500000000000:ℝ) ≤ Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (57397462127/500000000000:ℝ) ≤ taylorSin (115048559/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((3:ℝ) - x)) ≤ (63298149181/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (634684551/5000000000:ℝ) + taylorErr ≤ (63298149181/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (-991954320181/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (57397462127/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (63298149181/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9297841050571/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (4654864700839/500000000000:ℝ) := by nlinarith
  have hp1 : (15387913748777/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15407589159671/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1766454393217/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1950543754297/1000000000000:ℝ) := by nlinarith
  have hN : (1379204356699/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (21542765383117/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1379204356699/500000000000:ℝ) (21542765383117/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2561735901/10000000000000:ℝ) ≤ ((1379204356699/500000000000:ℝ)/(21542765383117/125000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_202 (x : ℝ) (h₁ : (6069/2048:ℝ) ≤ x) (h₂ : x ≤ (24307/8192:ℝ)) : (2229636307/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1031602079/10000000000:ℝ) ≤ Real.pi * ((3:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((3:ℝ) - x) ≤ (1150485591/10000000000:ℝ) := by nlinarith
  have hc1 : (198677841777/200000000000:ℝ) ≤ Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (198677841777/200000000000:ℝ) ≤ taylorCos (1150485591/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((3:ℝ) - x)) ≤ (994683705207/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1031602079/10000000000:ℝ) + taylorErr ≤ (994683705207/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (102977330661/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (102977330661/1000000000000:ℝ) ≤ taylorSin (1031602079/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((3:ℝ) - x)) ≤ (114794928877/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1150485591/10000000000:ℝ) + taylorErr ≤ (114794928877/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h, cos_flip (3:ℝ) x, sin_flip (3:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h, cos_flip (3:ℝ) x, sin_flip (3:ℝ) x]; ring
  have hcxl : (-994683705207/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-198677841777/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (102977330661/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (114794928877/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9309729401677/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1864323550557/200000000000:ℝ) := by nlinarith
  have hp1 : (15407588952993/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15427264364153/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1586632382301/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (35419434309/20000000000:ℝ) := by nlinarith
  have hN : (1290010795593/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (172785115058073/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1290010795593/500000000000:ℝ) (172785115058073/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (2229636307/10000000000000:ℝ) ≤ ((1290010795593/500000000000:ℝ)/(172785115058073/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_203 (x : ℝ) (h₁ : (6069/2048:ℝ) ≤ x) (h₂ : x ≤ (12169/4096:ℝ)) : (239478321/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (114089821/1250000000:ℝ) ≤ Real.pi * ((3:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((3:ℝ) - x) ≤ (1150485591/10000000000:ℝ) := by nlinarith
  have hc1 : (198677841777/200000000000:ℝ) ≤ Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (198677841777/200000000000:ℝ) ≤ taylorCos (1150485591/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((3:ℝ) - x)) ≤ (7966700937/8000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (114089821/1250000000:ℝ) + taylorErr ≤ (7966700937/8000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (22786295789/250000000000:ℝ) ≤ Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (22786295789/250000000000:ℝ) ≤ taylorSin (114089821/1250000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((3:ℝ) - x)) ≤ (114794928877/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1150485591/10000000000:ℝ) + taylorErr ≤ (114794928877/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h, cos_flip (3:ℝ) x, sin_flip (3:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h, cos_flip (3:ℝ) x, sin_flip (3:ℝ) x]; ring
  have hcxl : (-7966700937/8000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-198677841777/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (22786295789/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (114794928877/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9309729401677/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9333506103891/1000000000000:ℝ) := by nlinarith
  have hp1 : (15407588952993/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1930867446079/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (175540939639/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1773230329149/1000000000000:ℝ) := by nlinarith
  have hN : (2397716725997/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (86614336191371/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2397716725997/1000000000000:ℝ) (86614336191371/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (239478321/1250000000000:ℝ) ≤ ((2397716725997/1000000000000:ℝ)/(86614336191371/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_204 (x : ℝ) (h₁ : (6069/2048:ℝ) ≤ x) (h₂ : x ≤ (1525/512:ℝ)) : (1362675081/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (337475773/5000000000:ℝ) ≤ Real.pi * ((3:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((3:ℝ) - x) ≤ (1150485591/10000000000:ℝ) := by nlinarith
  have hc1 : (198677841777/200000000000:ℝ) ≤ Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (198677841777/200000000000:ℝ) ≤ taylorCos (1150485591/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((3:ℝ) - x)) ≤ (997723068911/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (337475773/5000000000:ℝ) + taylorErr ≤ (997723068911/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (13488783447/200000000000:ℝ) ≤ Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (13488783447/200000000000:ℝ) ≤ taylorSin (337475773/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((3:ℝ) - x)) ≤ (114794928877/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1150485591/10000000000:ℝ) + taylorErr ≤ (114794928877/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (-198677841777/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (13488783447/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (114794928877/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9309729401677/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9357282806103/1000000000000:ℝ) := by nlinarith
  have hp1 : (15407588952993/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15486289977591/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (129893519267/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1777747556547/1000000000000:ℝ) := by nlinarith
  have hN : (2032537363021/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (87058741513391/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2032537363021/1000000000000:ℝ) (87058741513391/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1362675081/10000000000000:ℝ) ≤ ((2032537363021/1000000000000:ℝ)/(87058741513391/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_205 (x : ℝ) (h₁ : (24307/8192:ℝ) ≤ x) (h₂ : x ≤ (12169/4096:ℝ)) : (240095521/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (114089821/1250000000:ℝ) ≤ Real.pi * ((3:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((3:ℝ) - x) ≤ (6447513/62500000:ℝ) := by nlinarith
  have hc1 : (15541932823/15625000000:ℝ) ≤ Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (15541932823/15625000000:ℝ) ≤ taylorCos (6447513/62500000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((3:ℝ) - x)) ≤ (7966700937/8000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (114089821/1250000000:ℝ) + taylorErr ≤ (7966700937/8000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (22786295789/250000000000:ℝ) ≤ Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (22786295789/250000000000:ℝ) ≤ taylorSin (114089821/1250000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((3:ℝ) - x)) ≤ (20595467057/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (6447513/62500000:ℝ) + taylorErr ≤ (20595467057/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h, cos_flip (3:ℝ) x, sin_flip (3:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h, cos_flip (3:ℝ) x, sin_flip (3:ℝ) x]; ring
  have hcxl : (-7966700937/8000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-15541932823/15625000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (22786295789/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (20595467057/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (582601109549/62500000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9333506103891/1000000000000:ℝ) := by nlinarith
  have hp1 : (1542726415721/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1930867446079/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (351530204301/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1590684675087/1000000000000:ℝ) := by nlinarith
  have hN : (600201129469/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (86614336191371/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (600201129469/250000000000:ℝ) (86614336191371/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (240095521/1250000000000:ℝ) ≤ ((600201129469/250000000000:ℝ)/(86614336191371/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_206 (x : ℝ) (h₁ : (12169/4096:ℝ) ≤ x) (h₂ : x ≤ (24369/8192:ℝ)) : (1635115293/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (793835057/10000000000:ℝ) ≤ Real.pi * ((3:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((3:ℝ) - x) ≤ (912718569/10000000000:ℝ) := by nlinarith
  have hc1 : (995837612591/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (995837612591/1000000000000:ℝ) ≤ taylorCos (912718569/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((3:ℝ) - x)) ≤ (99685078609/100000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (793835057/10000000000:ℝ) + taylorErr ≤ (99685078609/100000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (79300153989/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (79300153989/1000000000000:ℝ) ≤ taylorSin (793835057/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((3:ℝ) - x)) ≤ (4557259389/50000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (912718569/10000000000:ℝ) + taylorErr ≤ (4557259389/50000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h, cos_flip (3:ℝ) x, sin_flip (3:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h, cos_flip (3:ℝ) x, sin_flip (3:ℝ) x]; ring
  have hcxl : (-99685078609/100000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-995837612591/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (79300153989/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (4557259389/50000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (933350610389/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9345394454997/1000000000000:ℝ) := by nlinarith
  have hp1 : (7723469680713/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1933326846639/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1224944670019/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1409707507817/1000000000000:ℝ) := by nlinarith
  have hN : (222078228261/100000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (86836397519489/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (222078228261/100000000000:ℝ) (86836397519489/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1635115293/10000000000000:ℝ) ≤ ((222078228261/100000000000:ℝ)/(86836397519489/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_207 (x : ℝ) (h₁ : (12169/4096:ℝ) ≤ x) (h₂ : x ≤ (1525/512:ℝ)) : (136952521/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (337475773/5000000000:ℝ) ≤ Real.pi * ((3:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((3:ℝ) - x) ≤ (912718569/10000000000:ℝ) := by nlinarith
  have hc1 : (995837612591/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (995837612591/1000000000000:ℝ) ≤ taylorCos (912718569/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((3:ℝ) - x)) ≤ (997723068911/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (337475773/5000000000:ℝ) + taylorErr ≤ (997723068911/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (13488783447/200000000000:ℝ) ≤ Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (13488783447/200000000000:ℝ) ≤ taylorSin (337475773/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((3:ℝ) - x)) ≤ (4557259389/50000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (912718569/10000000000:ℝ) + taylorErr ≤ (4557259389/50000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (-995837612591/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (13488783447/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (4557259389/50000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (933350610389/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9357282806103/1000000000000:ℝ) := by nlinarith
  have hp1 : (7723469680713/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15486289977591/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (520901049913/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (176437601003/125000000000:ℝ) := by nlinarith
  have hN : (2037639712417/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (87058741513391/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2037639712417/1000000000000:ℝ) (87058741513391/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (136952521/1000000000000:ℝ) ≤ ((2037639712417/1000000000000:ℝ)/(87058741513391/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_208 (x : ℝ) (h₁ : (761/256:ℝ) ≤ x) (h₂ : x ≤ (3:ℝ)) : (318089829/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * ((3:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((3:ℝ) - x) ≤ (429514621/5000000000:ℝ) := by nlinarith
  have hc1 : (498156304957/500000000000:ℝ) ≤ Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (498156304957/500000000000:ℝ) ≤ taylorCos (429514621/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((3:ℝ) - x)) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((3:ℝ) - x)) ≤ (17159462937/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (429514621/5000000000:ℝ) + taylorErr ≤ (17159462937/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (-498156304957/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (17159462937/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9338875036647/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (942477796077/100000000000:ℝ) := by nlinarith
  have hp1 : (7727912468761/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3119598872863/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-35283/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (133826603093/100000000000:ℝ) := by nlinarith
  have hN : (996312574631/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (11040804951227/62500000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (996312574631/1000000000000:ℝ) (11040804951227/62500000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (318089829/10000000000000:ℝ) ≤ ((996312574631/1000000000000:ℝ)/(11040804951227/62500000000:ℝ))^2 := by norm_num
  linarith

theorem wc_209 (x : ℝ) (h₁ : (24369/8192:ℝ) ≤ x) (h₂ : x ≤ (1525/512:ℝ)) : (686336349/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (337475773/5000000000:ℝ) ≤ Real.pi * ((3:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((3:ℝ) - x) ≤ (396917529/5000000000:ℝ) := by nlinarith
  have hc1 : (498425390779/500000000000:ℝ) ≤ Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (498425390779/500000000000:ℝ) ≤ taylorCos (396917529/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((3:ℝ) - x)) ≤ (997723068911/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (337475773/5000000000:ℝ) + taylorErr ≤ (997723068911/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (13488783447/200000000000:ℝ) ≤ Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (13488783447/200000000000:ℝ) ≤ taylorSin (337475773/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((3:ℝ) - x)) ≤ (79300158613/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (396917529/5000000000:ℝ) + taylorErr ≤ (79300158613/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (-498425390779/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (13488783447/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (79300158613/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (2336348613749/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9357282806103/1000000000000:ℝ) := by nlinarith
  have hp1 : (15466614565641/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15486289977591/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (104312907267/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (24561305031/20000000000:ℝ) := by nlinarith
  have hN : (509994963557/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (87058741513391/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (509994963557/250000000000:ℝ) (87058741513391/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (686336349/5000000000000:ℝ) ≤ ((509994963557/250000000000:ℝ)/(87058741513391/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_210 (x : ℝ) (h₁ : (1525/512:ℝ) ≤ x) (h₂ : x ≤ (12231/4096:ℝ)) : (183106839/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (109296131/2500000000:ℝ) ≤ Real.pi * ((3:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((3:ℝ) - x) ≤ (674951547/10000000000:ℝ) := by nlinarith
  have hc1 : (49886153219/50000000000:ℝ) ≤ Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (49886153219/50000000000:ℝ) ≤ taylorCos (674951547/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((3:ℝ) - x)) ≤ (249761125731/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (109296131/2500000000:ℝ) + taylorErr ≤ (249761125731/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (43704524933/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (43704524933/1000000000000:ℝ) ≤ taylorSin (109296131/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((3:ℝ) - x)) ≤ (67443921859/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (674951547/10000000000:ℝ) + taylorErr ≤ (67443921859/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h, cos_flip (3:ℝ) x, sin_flip (3:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h, cos_flip (3:ℝ) x, sin_flip (3:ℝ) x]; ring
  have hcxl : (-249761125731/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-49886153219/50000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (43704524933/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (67443921859/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (4678641403051/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1876211901663/200000000000:ℝ) := by nlinarith
  have hp1 : (15486289769857/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (310512807731/20000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (338410468683/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (523555038521/500000000000:ℝ) := by nlinarith
  have hN : (837272000873/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (35001710999419/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (837272000873/500000000000:ℝ) (35001710999419/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (183106839/2000000000000:ℝ) ≤ ((837272000873/500000000000:ℝ)/(35001710999419/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_211 (x : ℝ) (h₁ : (1525/512:ℝ) ≤ x) (h₂ : x ≤ (6131/2048:ℝ)) : (137922559/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (99708751/5000000000:ℝ) ≤ Real.pi * ((3:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((3:ℝ) - x) ≤ (674951547/10000000000:ℝ) := by nlinarith
  have hc1 : (49886153219/50000000000:ℝ) ≤ Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (49886153219/50000000000:ℝ) ≤ taylorCos (674951547/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((3:ℝ) - x)) ≤ (999801172151/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (99708751/5000000000:ℝ) + taylorErr ≤ (999801172151/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (19940426247/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (19940426247/1000000000000:ℝ) ≤ taylorSin (99708751/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((3:ℝ) - x)) ≤ (67443921859/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (674951547/10000000000:ℝ) + taylorErr ≤ (67443921859/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h, cos_flip (3:ℝ) x, sin_flip (3:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h, cos_flip (3:ℝ) x, sin_flip (3:ℝ) x]; ring
  have hcxl : (-999801172151/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-49886153219/50000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (19940426247/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (67443921859/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (4678641403051/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9404836210527/1000000000000:ℝ) := by nlinarith
  have hp1 : (15486289769857/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15564990795509/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (61760643799/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1049764022949/1000000000000:ℝ) := by nlinarith
  have hN : (10452210267/8000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (2198773603671/12500000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (10452210267/8000000000:ℝ) (2198773603671/12500000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (137922559/2500000000000:ℝ) ≤ ((10452210267/8000000000:ℝ)/(2198773603671/12500000000:ℝ))^2 := by norm_num
  linarith

theorem wc_212 (x : ℝ) (h₁ : (1525/512:ℝ) ≤ x) (h₂ : x ≤ (3:ℝ)) : (318991089/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * ((3:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((3:ℝ) - x) ≤ (674951547/10000000000:ℝ) := by nlinarith
  have hc1 : (49886153219/50000000000:ℝ) ≤ Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (49886153219/50000000000:ℝ) ≤ taylorCos (674951547/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((3:ℝ) - x)) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((3:ℝ) - x)) ≤ (67443921859/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (674951547/10000000000:ℝ) + taylorErr ≤ (67443921859/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (-49886153219/50000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (67443921859/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (4678641403051/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (942477796077/100000000000:ℝ) := by nlinarith
  have hp1 : (15486289769857/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3119598872863/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-35283/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (131498739133/125000000000:ℝ) := by nlinarith
  have hN : (997723029097/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (11040804951227/62500000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (997723029097/1000000000000:ℝ) (11040804951227/62500000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (318991089/10000000000000:ℝ) ≤ ((997723029097/1000000000000:ℝ)/(11040804951227/62500000000:ℝ))^2 := by norm_num
  linarith

theorem wc_213 (x : ℝ) (h₁ : (1527/512:ℝ) ≤ x) (h₂ : x ≤ (3:ℝ)) : (319472457/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * ((3:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((3:ℝ) - x) ≤ (138058271/2500000000:ℝ) := by nlinarith
  have hc1 : (998475578309/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (998475578309/1000000000000:ℝ) ≤ taylorCos (138058271/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((3:ℝ) - x)) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((3:ℝ) - x)) ≤ (6899405831/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (138058271/2500000000:ℝ) + taylorErr ≤ (6899405831/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (-998475578309/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (6899405831/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1873910930481/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (942477796077/100000000000:ℝ) := by nlinarith
  have hp1 : (96916247863/6250000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3119598872863/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-35283/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (860935146153/1000000000000:ℝ) := by nlinarith
  have hN : (499237771513/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (11040804951227/62500000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (499237771513/500000000000:ℝ) (11040804951227/62500000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (319472457/10000000000000:ℝ) ≤ ((499237771513/500000000000:ℝ)/(11040804951227/62500000000:ℝ))^2 := by norm_num
  linarith

theorem wc_214 (x : ℝ) (h₁ : (12231/4096:ℝ) ≤ x) (h₂ : x ≤ (6131/2048:ℝ)) : (5534703/100000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (99708751/5000000000:ℝ) ≤ Real.pi * ((3:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((3:ℝ) - x) ≤ (17487381/400000000:ℝ) := by nlinarith
  have hc1 : (199808899679/200000000000:ℝ) ≤ Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (199808899679/200000000000:ℝ) ≤ taylorCos (17487381/400000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((3:ℝ) - x)) ≤ (999801172151/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (99708751/5000000000:ℝ) + taylorErr ≤ (999801172151/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (19940426247/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (19940426247/1000000000000:ℝ) ≤ taylorSin (99708751/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((3:ℝ) - x)) ≤ (43704529557/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (17487381/400000000:ℝ) + taylorErr ≤ (43704529557/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h, cos_flip (3:ℝ) x, sin_flip (3:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h, cos_flip (3:ℝ) x, sin_flip (3:ℝ) x]; ring
  have hcxl : (-999801172151/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-199808899679/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (19940426247/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (43704529557/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (4690529754157/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9404836210527/1000000000000:ℝ) := by nlinarith
  have hp1 : (970352511143/62500000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15564990795509/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (9674621341/31250000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (680260600277/1000000000000:ℝ) := by nlinarith
  have hN : (1308632381307/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (2198773603671/12500000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1308632381307/1000000000000:ℝ) (2198773603671/12500000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (5534703/100000000000:ℝ) ≤ ((1308632381307/1000000000000:ℝ)/(2198773603671/12500000000:ℝ))^2 := by norm_num
  linarith

theorem wc_215 (x : ℝ) (h₁ : (383/128:ℝ) ≤ x) (h₂ : x ≤ (3:ℝ)) : (10007991/312500000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * ((3:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((3:ℝ) - x) ≤ (245436927/10000000000:ℝ) := by nlinarith
  have hc1 : (62481176027/62500000000:ℝ) ≤ Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (62481176027/62500000000:ℝ) ≤ taylorCos (245436927/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((3:ℝ) - x)) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((3:ℝ) - x)) ≤ (24541230879/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (245436927/10000000000:ℝ) + taylorErr ≤ (24541230879/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (-62481176027/62500000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (24541230879/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9400234268163/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (942477796077/100000000000:ℝ) := by nlinarith
  have hp1 : (15557374378637/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3119598872863/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-35283/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (23924623809/62500000000:ℝ) := by nlinarith
  have hN : (999698781149/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (11040804951227/62500000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (999698781149/1000000000000:ℝ) (11040804951227/62500000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (10007991/312500000000:ℝ) ≤ ((999698781149/1000000000000:ℝ)/(11040804951227/62500000000:ℝ))^2 := by norm_num
  linarith

theorem wc_216 (x : ℝ) (h₁ : (6131/2048:ℝ) ≤ x) (h₂ : x ≤ (3:ℝ)) : (80080323/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * ((3:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((3:ℝ) - x) ≤ (199417503/10000000000:ℝ) := by nlinarith
  have hc1 : (7998409341/8000000000:ℝ) ≤ Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (7998409341/8000000000:ℝ) ≤ taylorCos (199417503/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((3:ℝ) - x)) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((3:ℝ) - x)) ≤ (19940430871/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (199417503/10000000000:ℝ) + taylorErr ≤ (19940430871/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (-7998409341/8000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (19940430871/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (4702418105263/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (942477796077/100000000000:ℝ) := by nlinarith
  have hp1 : (15564990586719/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3119598872863/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-35283/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (77757682087/250000000000:ℝ) := by nlinarith
  have hN : (499900566171/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (11040804951227/62500000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (499900566171/500000000000:ℝ) (11040804951227/62500000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (80080323/2500000000000:ℝ) ≤ ((499900566171/500000000000:ℝ)/(11040804951227/62500000000:ℝ))^2 := by norm_num
  linarith

theorem wc_217 (x : ℝ) (h₁ : (3069/1024:ℝ) ≤ x) (h₂ : x ≤ (3:ℝ)) : (80105391/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * ((3:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((3:ℝ) - x) ≤ (1438107/156250000:ℝ) := by nlinarith
  have hc1 : (999957642289/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((3:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (999957642289/1000000000000:ℝ) ≤ taylorCos (1438107/156250000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((3:ℝ) - x)) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * ((3:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((3:ℝ) - x)) ≤ (9203757117/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1438107/156250000:ℝ) + taylorErr ≤ (9203757117/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (-999957642289/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (9203757117/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (4707787038021/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (942477796077/100000000000:ℝ) := by nlinarith
  have hp1 : (3895690434729/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3119598872863/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-35283/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (71780075821/500000000000:ℝ) := by nlinarith
  have hN : (499978803503/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (11040804951227/62500000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (499978803503/500000000000:ℝ) (11040804951227/62500000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (80105391/2500000000000:ℝ) ≤ ((499978803503/500000000000:ℝ)/(11040804951227/62500000000:ℝ))^2 := by norm_num
  linarith

theorem wc_218 (x : ℝ) (h₁ : (3:ℝ) ≤ x) (h₂ : x ≤ (1537/512:ℝ)) : (13065663/500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (479369/78125000:ℝ) := by nlinarith
  have hc1 : (49999058651/50000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (49999058651/50000000000:ℝ) ≤ taylorCos (479369/78125000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (76698587/12500000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (479369/78125000:ℝ) + taylorErr ≤ (76698587/12500000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-500000001131/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-49999058651/50000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-76698587/12500000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1131/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9424777960769/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9430913883921/1000000000000:ℝ) := by nlinarith
  have hp1 : (7798997077541/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (7804074654281/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-95769839813/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (17653/500000000000:ℝ) := by nlinarith
  have hN : (904211333207/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (44221068342967/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (904211333207/1000000000000:ℝ) (44221068342967/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (13065663/500000000000:ℝ) ≤ ((904211333207/1000000000000:ℝ)/(44221068342967/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_219 (x : ℝ) (h₁ : (3:ℝ) ≤ x) (h₂ : x ≤ (3079/1024:ℝ)) : (70009749/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (214757311/10000000000:ℝ) := by nlinarith
  have hc1 : (62485587693/62500000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (62485587693/62500000000:ℝ) ≤ taylorCos (214757311/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (21474082607/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (214757311/10000000000:ℝ) + taylorErr ≤ (21474082607/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-500000001131/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-62485587693/62500000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-21474082607/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1131/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9424777960769/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (47231268459/5000000000:ℝ) := by nlinarith
  have hp1 : (7798997077541/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15633536669181/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-167857928937/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (8841/250000000000:ℝ) := by nlinarith
  have hN : (332026772607/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (177463417619691/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (332026772607/500000000000:ℝ) (177463417619691/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (70009749/5000000000000:ℝ) ≤ ((332026772607/500000000000:ℝ)/(177463417619691/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_220 (x : ℝ) (h₁ : (3:ℝ) ≤ x) (h₂ : x ≤ (3081/1024:ℝ)) : (102076243/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (138058271/5000000000:ℝ) := by nlinarith
  have hc1 : (999618820233/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (999618820233/1000000000000:ℝ) ≤ taylorCos (138058271/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (27608148059/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (138058271/5000000000:ℝ) + taylorErr ≤ (27608148059/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-500000001131/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-999618820233/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-27608148059/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1131/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9424777960769/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1181548701869/125000000000:ℝ) := by nlinarith
  have hp1 : (7798997077541/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15643691613429/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-431893354253/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (35387/1000000000000:ℝ) := by nlinarith
  have hN : (28386273299/50000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (35539067773141/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (28386273299/50000000000:ℝ) (35539067773141/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (102076243/10000000000000:ℝ) ≤ ((28386273299/50000000000:ℝ)/(35539067773141/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_221 (x : ℝ) (h₁ : (3:ℝ) ≤ x) (h₂ : x ≤ (771/256:ℝ)) : (28217469/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (0:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (36815539/1000000000:ℝ) := by nlinarith
  have hc1 : (999322382323/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (999322382323/1000000000000:ℝ) ≤ taylorCos (36815539/1000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (500000001131/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (0:ℝ) + taylorErr ≤ (500000001131/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (-1131/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (-1131/500000000000:ℝ) ≤ taylorSin (0:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (18403612647/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (36815539/1000000000:ℝ) + taylorErr ≤ (18403612647/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-500000001131/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-999322382323/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-18403612647/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (1131/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9424777960769/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9461593499679/1000000000000:ℝ) := by nlinarith
  have hp1 : (7798997077541/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (78294620149/5000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-576361544627/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (35421/1000000000000:ℝ) := by nlinarith
  have hN : (6608763089/15625000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (5563859472073/31250000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (6608763089/15625000000:ℝ) (5563859472073/31250000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (28217469/5000000000000:ℝ) ≤ ((6608763089/15625000000:ℝ)/(5563859472073/31250000000:ℝ))^2 := by norm_num
  linarith

theorem wc_222 (x : ℝ) (h₁ : (1537/512:ℝ) ≤ x) (h₂ : x ≤ (6163/2048:ℝ)) : (93531111/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (61359231/10000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (5829127/200000000:ℝ) := by nlinarith
  have hc1 : (124946911723/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (124946911723/125000000000:ℝ) ≤ taylorCos (5829127/200000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (199996235509/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (61359231/10000000000:ℝ) + taylorErr ≤ (199996235509/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (1227176467/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (1227176467/200000000000:ℝ) ≤ taylorSin (61359231/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (29141511057/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (5829127/200000000:ℝ) + taylorErr ≤ (29141511057/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-199996235509/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-124946911723/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-29141511057/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-1227176467/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (117886423549/12500000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (472696179787/50000000000:ℝ) := by nlinarith
  have hp1 : (15608149099193/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15646230349491/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-455954794731/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-95769766339/1000000000000:ℝ) := by nlinarith
  have hN : (543620499053/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (8887667135409/50000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (543620499053/1000000000000:ℝ) (8887667135409/50000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (93531111/10000000000000:ℝ) ≤ ((543620499053/1000000000000:ℝ)/(8887667135409/50000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_223 (x : ℝ) (h₁ : (1537/512:ℝ) ≤ x) (h₂ : x ≤ (771/256:ℝ)) : (28217469/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (61359231/10000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (36815539/1000000000:ℝ) := by nlinarith
  have hc1 : (999322382323/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (999322382323/1000000000000:ℝ) ≤ taylorCos (36815539/1000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (199996235509/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (61359231/10000000000:ℝ) + taylorErr ≤ (199996235509/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (1227176467/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (1227176467/200000000000:ℝ) ≤ taylorSin (61359231/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (18403612647/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (36815539/1000000000:ℝ) + taylorErr ≤ (18403612647/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-199996235509/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-999322382323/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-18403612647/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-1227176467/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (117886423549/12500000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9461593499679/1000000000000:ℝ) := by nlinarith
  have hp1 : (15608149099193/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (78294620149/5000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-576361544627/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-95769766339/1000000000000:ℝ) := by nlinarith
  have hN : (6608763089/15625000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (5563859472073/31250000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (6608763089/15625000000:ℝ) (5563859472073/31250000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (28217469/5000000000000:ℝ) ≤ ((6608763089/15625000000:ℝ)/(5563859472073/31250000000:ℝ))^2 := by norm_num
  linarith

theorem wc_224 (x : ℝ) (h₁ : (1537/512:ℝ) ≤ x) (h₂ : x ≤ (3089/1024:ℝ)) : (128333/125000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (61359231/10000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (130388367/2500000000:ℝ) := by nlinarith
  have hc1 : (998640215917/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (998640215917/1000000000000:ℝ) ≤ taylorCos (130388367/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (199996235509/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (61359231/10000000000:ℝ) + taylorErr ≤ (199996235509/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (1227176467/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (1227176467/200000000000:ℝ) ≤ taylorSin (61359231/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (26065853477/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (130388367/2500000000:ℝ) + taylorErr ≤ (26065853477/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-199996235509/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-998640215917/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-26065853477/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-1227176467/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (117886423549/12500000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (4738466653779/500000000000:ℝ) := by nlinarith
  have hp1 : (15608149099193/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15684311390419/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-817649925181/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-95769766339/1000000000000:ℝ) := by nlinarith
  have hN : (11311893171/62500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (35724905966361/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (11311893171/62500000000:ℝ) (35724905966361/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (128333/125000000000:ℝ) ≤ ((11311893171/62500000000:ℝ)/(35724905966361/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_225 (x : ℝ) (h₁ : (6153/2048:ℝ) ≤ x) (h₂ : x ≤ (771/256:ℝ)) : (28217469/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (13805827/1000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (36815539/1000000000:ℝ) := by nlinarith
  have hc1 : (999322382323/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (999322382323/1000000000000:ℝ) ≤ taylorCos (36815539/1000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (499952351673/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (13805827/1000000000:ℝ) + taylorErr ≤ (499952351673/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (552215447/40000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (552215447/40000000000:ℝ) ≤ taylorSin (13805827/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (18403612647/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (36815539/1000000000:ℝ) + taylorErr ≤ (18403612647/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-499952351673/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-999322382323/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-18403612647/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-552215447/40000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (471929189393/50000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9461593499679/1000000000000:ℝ) := by nlinarith
  have hp1 : (15620842779333/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (78294620149/5000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-576361544627/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-215651766947/1000000000000:ℝ) := by nlinarith
  have hN : (6608763089/15625000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (5563859472073/31250000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (6608763089/15625000000:ℝ) (5563859472073/31250000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (28217469/5000000000000:ℝ) ≤ ((6608763089/15625000000:ℝ)/(5563859472073/31250000000:ℝ))^2 := by norm_num
  linarith

theorem wc_226 (x : ℝ) (h₁ : (3079/1024:ℝ) ≤ x) (h₂ : x ≤ (771/256:ℝ)) : (28217469/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (21475731/1000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (36815539/1000000000:ℝ) := by nlinarith
  have hc1 : (999322382323/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (999322382323/1000000000000:ℝ) ≤ taylorCos (36815539/1000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (499884703807/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (21475731/1000000000:ℝ) + taylorErr ≤ (499884703807/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (21474077983/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (21474077983/1000000000000:ℝ) ≤ taylorSin (21475731/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (18403612647/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (36815539/1000000000:ℝ) + taylorErr ≤ (18403612647/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-499884703807/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-999322382323/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-18403612647/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-21474077983/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9446253691799/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9461593499679/1000000000000:ℝ) := by nlinarith
  have hp1 : (15633536459471/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (78294620149/5000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-576361544627/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-8392894527/25000000000:ℝ) := by nlinarith
  have hN : (6608763089/15625000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (5563859472073/31250000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (6608763089/15625000000:ℝ) (5563859472073/31250000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (28217469/5000000000000:ℝ) ≤ ((6608763089/15625000000:ℝ)/(5563859472073/31250000000:ℝ))^2 := by norm_num
  linarith

theorem wc_227 (x : ℝ) (h₁ : (3079/1024:ℝ) ≤ x) (h₂ : x ≤ (6173/2048:ℝ)) : (3586667/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (21475731/1000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (444854429/10000000000:ℝ) := by nlinarith
  have hc1 : (99901068359/100000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (99901068359/100000000000:ℝ) ≤ taylorCos (444854429/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (499884703807/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (21475731/1000000000:ℝ) + taylorErr ≤ (499884703807/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (21474077983/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (21474077983/1000000000000:ℝ) ≤ taylorSin (21475731/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (5558846771/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (444854429/10000000000:ℝ) + taylorErr ≤ (5558846771/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-499884703807/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-99901068359/100000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-5558846771/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-21474077983/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9446253691799/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9469263403619/1000000000000:ℝ) := by nlinarith
  have hp1 : (15633536459471/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15671617710111/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-348464486017/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-8392894527/25000000000:ℝ) := by nlinarith
  have hN : (75520427889/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (178333898814237/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (75520427889/250000000000:ℝ) (178333898814237/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (3586667/1250000000000:ℝ) ≤ ((75520427889/250000000000:ℝ)/(178333898814237/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_228 (x : ℝ) (h₁ : (3079/1024:ℝ) ≤ x) (h₂ : x ≤ (3089/1024:ℝ)) : (128333/125000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (21475731/1000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (130388367/2500000000:ℝ) := by nlinarith
  have hc1 : (998640215917/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (998640215917/1000000000000:ℝ) ≤ taylorCos (130388367/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (499884703807/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (21475731/1000000000:ℝ) + taylorErr ≤ (499884703807/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (21474077983/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (21474077983/1000000000000:ℝ) ≤ taylorSin (21475731/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (26065853477/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (130388367/2500000000:ℝ) + taylorErr ≤ (26065853477/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-499884703807/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-998640215917/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-26065853477/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-21474077983/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9446253691799/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (4738466653779/500000000000:ℝ) := by nlinarith
  have hp1 : (15633536459471/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15684311390419/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-817649925181/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-8392894527/25000000000:ℝ) := by nlinarith
  have hN : (11311893171/62500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (35724905966361/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (11311893171/62500000000:ℝ) (35724905966361/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (128333/125000000000:ℝ) ≤ ((11311893171/62500000000:ℝ)/(35724905966361/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_229 (x : ℝ) (h₁ : (6163/2048:ℝ) ≤ x) (h₂ : x ≤ (6173/2048:ℝ)) : (3586667/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (291456349/10000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (444854429/10000000000:ℝ) := by nlinarith
  have hc1 : (99901068359/100000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (99901068359/100000000000:ℝ) ≤ taylorCos (444854429/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (999575298311/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (291456349/10000000000:ℝ) + taylorErr ≤ (999575298311/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (227668019/7812500000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (227668019/7812500000:ℝ) ≤ taylorSin (291456349/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (5558846771/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (444854429/10000000000:ℝ) + taylorErr ≤ (5558846771/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-999575298311/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-99901068359/100000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-5558846771/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-227668019/7812500000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9453923595739/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9469263403619/1000000000000:ℝ) := by nlinarith
  have hp1 : (3911557534903/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15671617710111/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-348464486017/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-364763773/800000000:ℝ) := by nlinarith
  have hN : (75520427889/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (178333898814237/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (75520427889/250000000000:ℝ) (178333898814237/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (3586667/1250000000000:ℝ) ≤ ((75520427889/250000000000:ℝ)/(178333898814237/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_230 (x : ℝ) (h₁ : (6163/2048:ℝ) ≤ x) (h₂ : x ≤ (3089/1024:ℝ)) : (128333/125000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (291456349/10000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (130388367/2500000000:ℝ) := by nlinarith
  have hc1 : (998640215917/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (998640215917/1000000000000:ℝ) ≤ taylorCos (130388367/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (999575298311/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (291456349/10000000000:ℝ) + taylorErr ≤ (999575298311/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (227668019/7812500000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (227668019/7812500000:ℝ) ≤ taylorSin (291456349/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (26065853477/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (130388367/2500000000:ℝ) + taylorErr ≤ (26065853477/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-999575298311/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-998640215917/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-26065853477/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-227668019/7812500000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9453923595739/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (4738466653779/500000000000:ℝ) := by nlinarith
  have hp1 : (3911557534903/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15684311390419/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-817649925181/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-364763773/800000000:ℝ) := by nlinarith
  have hN : (11311893171/62500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (35724905966361/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (11311893171/62500000000:ℝ) (35724905966361/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (128333/125000000000:ℝ) ≤ ((11311893171/62500000000:ℝ)/(35724905966361/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_231 (x : ℝ) (h₁ : (771/256:ℝ) ≤ x) (h₂ : x ≤ (3089/1024:ℝ)) : (128333/125000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (368155389/10000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (130388367/2500000000:ℝ) := by nlinarith
  have hc1 : (998640215917/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (998640215917/1000000000000:ℝ) ≤ taylorCos (130388367/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (999322386851/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (368155389/10000000000:ℝ) + taylorErr ≤ (999322386851/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (3680722067/100000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (3680722067/100000000000:ℝ) ≤ taylorSin (368155389/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (26065853477/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (130388367/2500000000:ℝ) + taylorErr ≤ (26065853477/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-999322386851/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-998640215917/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-26065853477/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-3680722067/100000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (4730796749839/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (4738466653779/500000000000:ℝ) := by nlinarith
  have hp1 : (62635695279/4000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15684311390419/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-817649925181/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-72045183061/125000000000:ℝ) := by nlinarith
  have hN : (11311893171/62500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (35724905966361/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (11311893171/62500000000:ℝ) (35724905966361/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (128333/125000000000:ℝ) ≤ ((11311893171/62500000000:ℝ)/(35724905966361/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_232 (x : ℝ) (h₁ : (771/256:ℝ) ≤ x) (h₂ : x ≤ (6183/2048:ℝ)) : (278293/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (368155389/10000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (149563127/2500000000:ℝ) := by nlinarith
  have hc1 : (499105500547/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (499105500547/500000000000:ℝ) ≤ taylorCos (149563127/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (999322386851/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (368155389/10000000000:ℝ) + taylorErr ≤ (999322386851/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (3680722067/100000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (3680722067/100000000000:ℝ) ≤ taylorSin (368155389/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (59789573081/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (149563127/2500000000:ℝ) + taylorErr ≤ (59789573081/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-999322386851/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-499105500547/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-59789573081/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-3680722067/100000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (4730796749839/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9484603211497/1000000000000:ℝ) := by nlinarith
  have hp1 : (62635695279/4000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1962125633841/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-93851723183/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-72045183061/125000000000:ℝ) := by nlinarith
  have hN : (3730860579/62500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (178915396159079/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3730860579/62500000000:ℝ) (178915396159079/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (278293/2500000000000:ℝ) ≤ ((3730860579/62500000000:ℝ)/(178915396159079/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_233 (x : ℝ) (h₁ : (6173/2048:ℝ) ≤ x) (h₂ : x ≤ (12361/4096:ℝ)) : (906687/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (111213607/2500000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (139975747/2500000000:ℝ) := by nlinarith
  have hc1 : (499216475201/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (499216475201/500000000000:ℝ) ≤ taylorCos (139975747/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (499505344059/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (111213607/2500000000:ℝ) + taylorErr ≤ (499505344059/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (5558846193/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (5558846193/125000000000:ℝ) ≤ taylorSin (111213607/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (55961051523/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (139975747/2500000000:ℝ) + taylorErr ≤ (55961051523/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-499505344059/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-499216475201/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-55961051523/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-5558846193/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (4734631701809/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1185096032441/125000000000:ℝ) := by nlinarith
  have hp1 : (1567161749989/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (627626329223/40000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-878065733671/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-696928890219/1000000000000:ℝ) := by nlinarith
  have hN : (120367216731/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (44692483395437/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (120367216731/1000000000000:ℝ) (44692483395437/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (906687/2000000000000:ℝ) ≤ ((120367216731/1000000000000:ℝ)/(44692483395437/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_234 (x : ℝ) (h₁ : (6173/2048:ℝ) ≤ x) (h₂ : x ≤ (6183/2048:ℝ)) : (278293/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (111213607/2500000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (149563127/2500000000:ℝ) := by nlinarith
  have hc1 : (499105500547/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (499105500547/500000000000:ℝ) ≤ taylorCos (149563127/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (499505344059/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (111213607/2500000000:ℝ) + taylorErr ≤ (499505344059/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (5558846193/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (5558846193/125000000000:ℝ) ≤ taylorSin (111213607/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (59789573081/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (149563127/2500000000:ℝ) + taylorErr ≤ (59789573081/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-499505344059/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-499105500547/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-59789573081/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-5558846193/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (4734631701809/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9484603211497/1000000000000:ℝ) := by nlinarith
  have hp1 : (1567161749989/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1962125633841/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-93851723183/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-696928890219/1000000000000:ℝ) := by nlinarith
  have hN : (3730860579/62500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (178915396159079/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3730860579/62500000000:ℝ) (178915396159079/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (278293/2500000000000:ℝ) ≤ ((3730860579/62500000000:ℝ)/(178915396159079/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_235 (x : ℝ) (h₁ : (12351/4096:ℝ) ≤ x) (h₂ : x ≤ (6183/2048:ℝ)) : (278293/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (120800987/2500000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (149563127/2500000000:ℝ) := by nlinarith
  have hc1 : (499105500547/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (499105500547/500000000000:ℝ) ≤ taylorCos (149563127/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (998832799117/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (120800987/2500000000:ℝ) + taylorErr ≤ (998832799117/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (48301591169/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (48301591169/1000000000000:ℝ) ≤ taylorSin (120800987/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (59789573081/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (149563127/2500000000:ℝ) + taylorErr ≤ (59789573081/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-998832799117/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-499105500547/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-59789573081/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-48301591169/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9473098355587/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9484603211497/1000000000000:ℝ) := by nlinarith
  have hp1 : (15677964339959/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1962125633841/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-93851723183/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-75727062391/100000000000:ℝ) := by nlinarith
  have hN : (3730860579/62500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (178915396159079/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3730860579/62500000000:ℝ) (178915396159079/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (278293/2500000000000:ℝ) ≤ ((3730860579/62500000000:ℝ)/(178915396159079/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_236 (x : ℝ) (h₁ : (3089/1024:ℝ) ≤ x) (h₂ : x ≤ (6183/2048:ℝ)) : (278293/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (521553467/10000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (149563127/2500000000:ℝ) := by nlinarith
  have hc1 : (499105500547/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (499105500547/500000000000:ℝ) ≤ taylorCos (149563127/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (998640220447/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (521553467/10000000000:ℝ) + taylorErr ≤ (998640220447/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (5213170233/100000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (5213170233/100000000000:ℝ) ≤ taylorSin (521553467/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (59789573081/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (149563127/2500000000:ℝ) + taylorErr ≤ (59789573081/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-998640220447/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-499105500547/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-59789573081/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-5213170233/100000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9476933307557/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9484603211497/1000000000000:ℝ) := by nlinarith
  have hp1 : (15684311180029/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1962125633841/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-93851723183/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-102206230211/125000000000:ℝ) := by nlinarith
  have hN : (3730860579/62500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (178915396159079/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3730860579/62500000000:ℝ) (178915396159079/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (278293/2500000000000:ℝ) ≤ ((3730860579/62500000000:ℝ)/(178915396159079/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_237 (x : ℝ) (h₁ : (12371/4096:ℝ) ≤ x) (h₂ : x ≤ (12381/4096:ℝ)) : (329/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (318301013/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (713301067/10000000000:ℝ) := by nlinarith
  have hc1 : (997457084143/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (997457084143/1000000000000:ℝ) ≤ taylorCos (713301067/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (199594875159/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (318301013/5000000000:ℝ) + taylorErr ≤ (199594875159/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (318086053/5000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (318086053/5000000000:ℝ) ≤ taylorSin (318301013/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (71269636607/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (713301067/10000000000:ℝ) + taylorErr ≤ (71269636607/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-199594875159/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-997457084143/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-71269636607/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-318086053/5000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (4744219081733/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9496108067407/1000000000000:ℝ) := by nlinarith
  have hp1 : (15703351700237/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (7858022795597/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-140009607273/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-999003432239/1000000000000:ℝ) := by nlinarith
  have hN : (257264111/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (35870427371149/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (257264111/250000000000:ℝ) (35870427371149/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (329/10000000000000:ℝ) ≤ ((257264111/250000000000:ℝ)/(35870427371149/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_238 (x : ℝ) (h₁ : (12371/4096:ℝ) ≤ x) (h₂ : x ≤ (6193/2048:ℝ)) : (41/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (318301013/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (751650587/10000000000:ℝ) := by nlinarith
  have hc1 : (498588217233/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (498588217233/500000000000:ℝ) ≤ taylorCos (751650587/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (199594875159/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (318301013/5000000000:ℝ) + taylorErr ≤ (199594875159/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (318086053/5000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (318086053/5000000000:ℝ) ≤ taylorSin (318301013/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-199594875159/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-498588217233/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-75094303203/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-318086053/5000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (4744219081733/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (593746438711/62500000000:ℝ) := by nlinarith
  have hp1 : (15703351700237/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15722392431347/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1180662104317/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-999003432239/1000000000000:ℝ) := by nlinarith
  have hN : (257264111/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (89748917371391/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (257264111/250000000000:ℝ) (89748917371391/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (41/1250000000000:ℝ) ≤ ((257264111/250000000000:ℝ)/(89748917371391/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_239 (x : ℝ) (h₁ : (1547/512:ℝ) ≤ x) (h₂ : x ≤ (24767/8192:ℝ)) : (593183/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (337475773/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (732475827/10000000000:ℝ) := by nlinarith
  have hc1 : (249329648183/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (249329648183/250000000000:ℝ) ≤ taylorCos (732475827/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (997723068911/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (337475773/5000000000:ℝ) + taylorErr ≤ (997723068911/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (13488783447/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (13488783447/200000000000:ℝ) ≤ taylorSin (337475773/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-997723068911/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-249329648183/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-1829552611/25000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-13488783447/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (2373068278859/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9498025543391/1000000000000:ℝ) := by nlinarith
  have hp1 : (15709698540307/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1571921901127/100000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-575182763699/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1059523608139/1000000000000:ℝ) := by nlinarith
  have hN : (15450134807/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (22428122305727/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (15450134807/250000000000:ℝ) (22428122305727/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (593183/5000000000000:ℝ) ≤ ((15450134807/250000000000:ℝ)/(22428122305727/125000000000:ℝ))^2 := by norm_num
  linarith

end Zeta23Ext.Bridge.FourPoint
