import FourPoint.Base

noncomputable section
open Real
namespace Zeta23Ext.Bridge.FourPoint


theorem wc_540 (x : ℝ) (h₁ : (12441/4096:ℝ) ≤ x) (h₂ : x ≤ (1557/512:ℝ)) : (111118793/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (586747651/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (644271931/5000000000:ℝ) := by nlinarith
  have hc1 : (198341950281/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (198341950281/200000000000:ℝ) ≤ taylorCos (644271931/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (993122444101/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (586747651/5000000000:ℝ) + taylorErr ≤ (993122444101/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (117080378313/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (117080378313/1000000000000:ℝ) ≤ taylorSin (586747651/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-993122444101/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-198341950281/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-128498113073/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-117080378313/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (4771063745521/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1194204043369/125000000000:ℝ) := by nlinarith
  have hp1 : (3948051865303/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (7905624096757/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-507928889549/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-462239405989/250000000000:ℝ) := by nlinarith
  have hN : (171167035971/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (11346486377591/62500000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (171167035971/200000000000:ℝ) (11346486377591/62500000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (111118793/5000000000000:ℝ) ≤ ((171167035971/200000000000:ℝ)/(11346486377591/62500000000:ℝ))^2 := by norm_num
  linarith

theorem wc_541 (x : ℝ) (h₁ : (24887/8192:ℝ) ≤ x) (h₂ : x ≤ (12451/4096:ℝ)) : (238838563/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (596335031/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (1250194343/10000000000:ℝ) := by nlinarith
  have hc1 : (496097620907/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (496097620907/500000000000:ℝ) ≤ taylorCos (1250194343/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (496448059853/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (596335031/5000000000:ℝ) + taylorErr ≤ (496448059853/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (59492225179/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (59492225179/500000000000:ℝ) ≤ taylorSin (596335031/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (124694018291/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1250194343/10000000000:ℝ) + taylorErr ≤ (124694018291/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-496448059853/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-496097620907/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-124694018291/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-59492225179/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9544044967027/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9549797394983/1000000000000:ℝ) := by nlinarith
  have hp1 : (15795380881247/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (197561266917/12500000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-492694164611/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-37588094247/20000000000:ℝ) := by nlinarith
  have hN : (221627148161/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (181397260570449/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (221627148161/250000000000:ℝ) (181397260570449/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (238838563/10000000000000:ℝ) ≤ ((221627148161/250000000000:ℝ)/(181397260570449/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_542 (x : ℝ) (h₁ : (6223/2048:ℝ) ≤ x) (h₂ : x ≤ (1557/512:ℝ)) : (255244651/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (605922411/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (644271931/5000000000:ℝ) := by nlinarith
  have hc1 : (198341950281/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (198341950281/200000000000:ℝ) ≤ taylorCos (644271931/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (248166536179/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (605922411/5000000000:ℝ) + taylorErr ≤ (248166536179/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (120888084931/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (120888084931/1000000000000:ℝ) ≤ taylorSin (605922411/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-248166536179/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-198341950281/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-128498113073/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-120888084931/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (2386490610753/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1194204043369/125000000000:ℝ) := by nlinarith
  have hp1 : (7899277150641/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (7905624096757/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-507928889549/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-23873212177/12500000000:ℝ) := by nlinarith
  have hN : (229297707361/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (11346486377591/62500000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (229297707361/250000000000:ℝ) (11346486377591/62500000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (255244651/10000000000000:ℝ) ≤ ((229297707361/250000000000:ℝ)/(11346486377591/62500000000:ℝ))^2 := by norm_num
  linarith

theorem wc_543 (x : ℝ) (h₁ : (6223/2048:ℝ) ≤ x) (h₂ : x ≤ (12461/4096:ℝ)) : (10193319/400000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (605922411/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (663446691/5000000000:ℝ) := by nlinarith
  have hc1 : (247802419017/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (247802419017/250000000000:ℝ) ≤ taylorCos (663446691/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (248166536179/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (605922411/5000000000:ℝ) + taylorErr ≤ (248166536179/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (120888084931/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (120888084931/1000000000000:ℝ) ≤ taylorSin (605922411/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (66150159077/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (663446691/5000000000:ℝ) + taylorErr ≤ (66150159077/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-248166536179/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-247802419017/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-66150159077/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-120888084931/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (2386490610753/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (4778733649461/500000000000:ℝ) := by nlinarith
  have hp1 : (7899277150641/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15817595033669/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1046336427693/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-23873212177/12500000000:ℝ) := by nlinarith
  have hN : (229297707361/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (181690362339927/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (229297707361/250000000000:ℝ) (181690362339927/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (10193319/400000000000:ℝ) ≤ ((229297707361/250000000000:ℝ)/(181690362339927/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_544 (x : ℝ) (h₁ : (6223/2048:ℝ) ≤ x) (h₂ : x ≤ (6233/2048:ℝ)) : (25442213/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (605922411/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (682621451/5000000000:ℝ) := by nlinarith
  have hc1 : (99069502317/100000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (99069502317/100000000000:ℝ) ≤ taylorCos (682621451/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (248166536179/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (605922411/5000000000:ℝ) + taylorErr ≤ (248166536179/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (120888084931/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (120888084931/1000000000000:ℝ) ≤ taylorSin (605922411/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (27220115503/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (682621451/5000000000:ℝ) + taylorErr ≤ (27220115503/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-248166536179/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-99069502317/100000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-27220115503/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-120888084931/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (2386490610753/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2390325562723/250000000000:ℝ) := by nlinarith
  have hp1 : (7899277150641/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (494498183557/31250000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-269205953449/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-23873212177/12500000000:ℝ) := by nlinarith
  have hN : (229297707361/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (7273480058633/40000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (229297707361/250000000000:ℝ) (7273480058633/40000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (25442213/1000000000000:ℝ) ≤ ((229297707361/250000000000:ℝ)/(7273480058633/40000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_545 (x : ℝ) (h₁ : (6223/2048:ℝ) ≤ x) (h₂ : x ≤ (3119/1024:ℝ)) : (63400731/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (605922411/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (1441941941/10000000000:ℝ) := by nlinarith
  have hc1 : (197924403039/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (197924403039/200000000000:ℝ) ≤ taylorCos (1441941941/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (248166536179/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (605922411/5000000000:ℝ) + taylorErr ≤ (248166536179/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (120888084931/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (120888084931/1000000000000:ℝ) ≤ taylorSin (605922411/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (143695035451/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1441941941/10000000000:ℝ) + taylorErr ≤ (143695035451/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-248166536179/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-197924403039/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-143695035451/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-120888084931/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (2386490610753/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9568972154831/1000000000000:ℝ) := by nlinarith
  have hp1 : (7899277150641/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15836635554133/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-142227869211/62500000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-23873212177/12500000000:ℝ) := by nlinarith
  have hN : (229297707361/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (182130456199863/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (229297707361/250000000000:ℝ) (182130456199863/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (63400731/2500000000000:ℝ) ≤ ((229297707361/250000000000:ℝ)/(182130456199863/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_546 (x : ℝ) (h₁ : (389/128:ℝ) ≤ x) (h₂ : x ≤ (1587/512:ℝ)) : (249212333/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/1000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (391165101/1250000000:ℝ) := by nlinarith
  have hc1 : (190287003737/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (190287003737/200000000000:ℝ) ≤ taylorCos (391165101/1250000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (198495907373/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/1000000000:ℝ) + taylorErr ≤ (198495907373/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (61205336453/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (61205336453/500000000000:ℝ) ≤ taylorSin (122718463/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (76962410593/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (391165101/1250000000:ℝ) + taylorErr ≤ (76962410593/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-198495907373/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-190287003737/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-76962410593/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-61205336453/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (47737482119/5000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9737710041499/1000000000000:ℝ) := by nlinarith
  have hp1 : (1580109303731/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (16115896520943/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-4961272980477/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1934222431347/1000000000000:ℝ) := by nlinarith
  have hN : (470871447241/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (188645993704621/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (470871447241/500000000000:ℝ) (188645993704621/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (249212333/10000000000000:ℝ) ≤ ((470871447241/500000000000:ℝ)/(188645993704621/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_547 (x : ℝ) (h₁ : (389/128:ℝ) ≤ x) (h₂ : x ≤ (809/256:ℝ)) : (115281189/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/1000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (1006291397/2000000000:ℝ) := by nlinarith
  have hc1 : (876070091897/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (876070091897/1000000000000:ℝ) ≤ taylorCos (1006291397/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (198495907373/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/1000000000:ℝ) + taylorErr ≤ (198495907373/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (61205336453/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (61205336453/500000000000:ℝ) ≤ taylorSin (122718463/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-198495907373/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-876070091897/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-241091887203/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-61205336453/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (47737482119/5000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2481980914799/250000000000:ℝ) := by nlinarith
  have hp1 : (1580109303731/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (16430699792617/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-990327105267/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1934222431347/1000000000000:ℝ) := by nlinarith
  have hN : (470871447241/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (12257958522853/62500000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (470871447241/500000000000:ℝ) (12257958522853/62500000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (115281189/5000000000000:ℝ) ≤ ((470871447241/500000000000:ℝ)/(12257958522853/62500000000:ℝ))^2 := by norm_num
  linarith

theorem wc_548 (x : ℝ) (h₁ : (12451/4096:ℝ) ≤ x) (h₂ : x ≤ (12461/4096:ℝ)) : (290088193/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (625097171/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (663446691/5000000000:ℝ) := by nlinarith
  have hc1 : (247802419017/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (247802419017/250000000000:ℝ) ≤ taylorCos (663446691/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (19843904927/20000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (625097171/5000000000:ℝ) + taylorErr ≤ (19843904927/20000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (124694013667/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (124694013667/1000000000000:ℝ) ≤ taylorSin (625097171/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (66150159077/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (663446691/5000000000:ℝ) + taylorErr ≤ (66150159077/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-19843904927/20000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-247802419017/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-66150159077/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-124694013667/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (4774898697491/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (4778733649461/500000000000:ℝ) := by nlinarith
  have hp1 : (1975612642669/125000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15817595033669/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1046336427693/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-78831062357/40000000000:ℝ) := by nlinarith
  have hN : (39143252503/40000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (181690362339927/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (39143252503/40000000000:ℝ) (181690362339927/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (290088193/10000000000000:ℝ) ≤ ((39143252503/40000000000:ℝ)/(181690362339927/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_549 (x : ℝ) (h₁ : (12451/4096:ℝ) ≤ x) (h₂ : x ≤ (6233/2048:ℝ)) : (289620509/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (625097171/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (682621451/5000000000:ℝ) := by nlinarith
  have hc1 : (99069502317/100000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (99069502317/100000000000:ℝ) ≤ taylorCos (682621451/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (19843904927/20000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (625097171/5000000000:ℝ) + taylorErr ≤ (19843904927/20000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (124694013667/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (124694013667/1000000000000:ℝ) ≤ taylorSin (625097171/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (27220115503/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (682621451/5000000000:ℝ) + taylorErr ≤ (27220115503/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-19843904927/20000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-99069502317/100000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-27220115503/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-124694013667/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (4774898697491/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2390325562723/250000000000:ℝ) := by nlinarith
  have hp1 : (1975612642669/125000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (494498183557/31250000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-269205953449/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-78831062357/40000000000:ℝ) := by nlinarith
  have hN : (39143252503/40000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (7273480058633/40000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (39143252503/40000000000:ℝ) (7273480058633/40000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (289620509/10000000000000:ℝ) ≤ ((39143252503/40000000000:ℝ)/(7273480058633/40000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_550 (x : ℝ) (h₁ : (1557/512:ℝ) ≤ x) (h₂ : x ≤ (6233/2048:ℝ)) : (65423973/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1288543861/10000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (682621451/5000000000:ℝ) := by nlinarith
  have hc1 : (99069502317/100000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (99069502317/100000000000:ℝ) ≤ taylorCos (682621451/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (495854877971/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1288543861/10000000000:ℝ) + taylorErr ≤ (495854877971/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (2569962169/20000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (2569962169/20000000000:ℝ) ≤ taylorSin (1288543861/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (27220115503/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (682621451/5000000000:ℝ) + taylorErr ≤ (27220115503/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-495854877971/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-99069502317/100000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-27220115503/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-2569962169/20000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9553632346951/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2390325562723/250000000000:ℝ) := by nlinarith
  have hp1 : (15811247981421/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (494498183557/31250000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-269205953449/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1015857728923/500000000000:ℝ) := by nlinarith
  have hN : (65000356369/62500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (7273480058633/40000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (65000356369/62500000000:ℝ) (7273480058633/40000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (65423973/2000000000000:ℝ) ≤ ((65000356369/62500000000:ℝ)/(7273480058633/40000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_551 (x : ℝ) (h₁ : (1557/512:ℝ) ≤ x) (h₂ : x ≤ (12471/4096:ℝ)) : (326592691/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1288543861/10000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (1403592421/10000000000:ℝ) := by nlinarith
  have hc1 : (495082900147/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (495082900147/500000000000:ℝ) ≤ taylorCos (1403592421/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (495854877971/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1288543861/10000000000:ℝ) + taylorErr ≤ (495854877971/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (2569962169/20000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (2569962169/20000000000:ℝ) ≤ taylorSin (1288543861/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (4371838599/31250000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1403592421/10000000000:ℝ) + taylorErr ≤ (4371838599/31250000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-495854877971/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-495082900147/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-4371838599/31250000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-2569962169/20000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9553632346951/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9565137202861/1000000000000:ℝ) := by nlinarith
  have hp1 : (15811247981421/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (7915144356989/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2214638951459/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1015857728923/500000000000:ℝ) := by nlinarith
  have hN : (65000356369/62500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (22747962427389/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (65000356369/62500000000:ℝ) (22747962427389/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (326592691/10000000000000:ℝ) ≤ ((65000356369/62500000000:ℝ)/(22747962427389/125000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_552 (x : ℝ) (h₁ : (1557/512:ℝ) ≤ x) (h₂ : x ≤ (3119/1024:ℝ)) : (326066581/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1288543861/10000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (1441941941/10000000000:ℝ) := by nlinarith
  have hc1 : (197924403039/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (197924403039/200000000000:ℝ) ≤ taylorCos (1441941941/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (495854877971/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1288543861/10000000000:ℝ) + taylorErr ≤ (495854877971/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (2569962169/20000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (2569962169/20000000000:ℝ) ≤ taylorSin (1288543861/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (143695035451/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1441941941/10000000000:ℝ) + taylorErr ≤ (143695035451/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-495854877971/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-197924403039/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-143695035451/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-2569962169/20000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9553632346951/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9568972154831/1000000000000:ℝ) := by nlinarith
  have hp1 : (15811247981421/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15836635554133/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-142227869211/62500000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1015857728923/500000000000:ℝ) := by nlinarith
  have hN : (65000356369/62500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (182130456199863/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (65000356369/62500000000:ℝ) (182130456199863/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (326066581/10000000000000:ℝ) ≤ ((65000356369/62500000000:ℝ)/(182130456199863/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_553 (x : ℝ) (h₁ : (1557/512:ℝ) ≤ x) (h₂ : x ≤ (6243/2048:ℝ)) : (325017537/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1288543861/10000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (1518640981/10000000000:ℝ) := by nlinarith
  have hc1 : (61780674411/62500000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (61780674411/62500000000:ℝ) ≤ taylorCos (1518640981/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (495854877971/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1288543861/10000000000:ℝ) + taylorErr ≤ (495854877971/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (2569962169/20000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (2569962169/20000000000:ℝ) ≤ taylorSin (1288543861/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (75640520159/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1518640981/10000000000:ℝ) + taylorErr ≤ (75640520159/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-495854877971/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-61780674411/62500000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-75640520159/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-2569962169/20000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9553632346951/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9576642058771/1000000000000:ℝ) := by nlinarith
  have hp1 : (15811247981421/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3962332308611/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-239770301493/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1015857728923/500000000000:ℝ) := by nlinarith
  have hN : (65000356369/62500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (45606036560911/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (65000356369/62500000000:ℝ) (45606036560911/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (325017537/10000000000000:ℝ) ≤ ((65000356369/62500000000:ℝ)/(45606036560911/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_554 (x : ℝ) (h₁ : (1557/512:ℝ) ≤ x) (h₂ : x ≤ (781/256:ℝ)) : (161986357/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1288543861/10000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (79767001/500000000:ℝ) := by nlinarith
  have hc1 : (493650707943/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (493650707943/500000000000:ℝ) ≤ taylorCos (79767001/500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (495854877971/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1288543861/10000000000:ℝ) + taylorErr ≤ (495854877971/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (2569962169/20000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (2569962169/20000000000:ℝ) ≤ taylorSin (1288543861/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-495854877971/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-493650707943/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-31771629131/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-2569962169/20000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9553632346951/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (958431196271/100000000000:ℝ) := by nlinarith
  have hp1 : (15811247981421/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (247844108043/15625000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-100792461863/40000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1015857728923/500000000000:ℝ) := by nlinarith
  have hN : (65000356369/62500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (182718071597093/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (65000356369/62500000000:ℝ) (182718071597093/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (161986357/5000000000000:ℝ) ≤ ((65000356369/62500000000:ℝ)/(182718071597093/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_555 (x : ℝ) (h₁ : (1557/512:ℝ) ≤ x) (h₂ : x ≤ (3129/1024:ℝ)) : (160947823/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1288543861/10000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (1748738099/10000000000:ℝ) := by nlinarith
  have hc1 : (492374249763/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (492374249763/500000000000:ℝ) ≤ taylorCos (1748738099/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (495854877971/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1288543861/10000000000:ℝ) + taylorErr ≤ (495854877971/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (2569962169/20000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (2569962169/20000000000:ℝ) ≤ taylorSin (1288543861/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (173983875729/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1748738099/10000000000:ℝ) + taylorErr ≤ (173983875729/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-495854877971/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-492374249763/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-173983875729/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-2569962169/20000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9553632346951/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9599651770589/1000000000000:ℝ) := by nlinarith
  have hp1 : (15811247981421/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3971852568843/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1382076607503/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1015857728923/500000000000:ℝ) := by nlinarith
  have hN : (65000356369/62500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (91653314116573/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (65000356369/62500000000:ℝ) (91653314116573/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (160947823/5000000000000:ℝ) ≤ ((65000356369/62500000000:ℝ)/(91653314116573/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_556 (x : ℝ) (h₁ : (1557/512:ℝ) ≤ x) (h₂ : x ≤ (1567/512:ℝ)) : (63967043/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1288543861/10000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (1902136177/10000000000:ℝ) := by nlinarith
  have hc1 : (981963866847/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (981963866847/1000000000000:ℝ) ≤ taylorCos (1902136177/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (495854877971/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1288543861/10000000000:ℝ) + taylorErr ≤ (495854877971/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (2569962169/20000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (2569962169/20000000000:ℝ) ≤ taylorSin (1288543861/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (94534333207/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1902136177/10000000000:ℝ) + taylorErr ≤ (94534333207/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-495854877971/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-981963866847/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-94534333207/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-2569962169/20000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9553632346951/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2403747894617/250000000000:ℝ) := by nlinarith
  have hp1 : (15811247981421/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15912797635991/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-3008611427953/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1015857728923/500000000000:ℝ) := by nlinarith
  have hN : (65000356369/62500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (91948063054011/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (65000356369/62500000000:ℝ) (91948063054011/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (63967043/2000000000000:ℝ) ≤ ((65000356369/62500000000:ℝ)/(91948063054011/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_557 (x : ℝ) (h₁ : (1557/512:ℝ) ≤ x) (h₂ : x ≤ (393/128:ℝ)) : (157881813/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1288543861/10000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (441786467/2000000000:ℝ) := by nlinarith
  have hc1 : (975702127767/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (975702127767/1000000000000:ℝ) ≤ taylorCos (441786467/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (495854877971/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1288543861/10000000000:ℝ) + taylorErr ≤ (495854877971/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (2569962169/20000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (2569962169/20000000000:ℝ) ≤ taylorSin (1288543861/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (109550621231/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (441786467/2000000000:ℝ) + taylorErr ≤ (109550621231/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-495854877971/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-975702127767/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-109550621231/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-2569962169/20000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9553632346951/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (385826847769/40000000000:ℝ) := by nlinarith
  have hp1 : (15811247981421/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3990893089307/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-3497638537601/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1015857728923/500000000000:ℝ) := by nlinarith
  have hN : (65000356369/62500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (46269486393551/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (65000356369/62500000000:ℝ) (46269486393551/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (157881813/5000000000000:ℝ) ≤ ((65000356369/62500000000:ℝ)/(46269486393551/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_558 (x : ℝ) (h₁ : (12461/4096:ℝ) ≤ x) (h₂ : x ≤ (12471/4096:ℝ)) : (9158301/250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1326893381/10000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (1403592421/10000000000:ℝ) := by nlinarith
  have hc1 : (495082900147/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (495082900147/500000000000:ℝ) ≤ taylorCos (1403592421/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (198241936121/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1326893381/10000000000:ℝ) + taylorErr ≤ (198241936121/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (132300313531/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (132300313531/1000000000000:ℝ) ≤ taylorSin (1326893381/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (4371838599/31250000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1403592421/10000000000:ℝ) + taylorErr ≤ (4371838599/31250000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-198241936121/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-495082900147/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-4371838599/31250000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-132300313531/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9557467298921/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9565137202861/1000000000000:ℝ) := by nlinarith
  have hp1 : (15817594821491/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (7915144356989/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2214638951459/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2092672754189/1000000000000:ℝ) := by nlinarith
  have hN : (68841442099/62500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (22747962427389/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (68841442099/62500000000:ℝ) (22747962427389/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (9158301/250000000000:ℝ) ≤ ((68841442099/62500000000:ℝ)/(22747962427389/125000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_559 (x : ℝ) (h₁ : (12461/4096:ℝ) ≤ x) (h₂ : x ≤ (3119/1024:ℝ)) : (365741913/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1326893381/10000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (1441941941/10000000000:ℝ) := by nlinarith
  have hc1 : (197924403039/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (197924403039/200000000000:ℝ) ≤ taylorCos (1441941941/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (198241936121/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1326893381/10000000000:ℝ) + taylorErr ≤ (198241936121/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (132300313531/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (132300313531/1000000000000:ℝ) ≤ taylorSin (1326893381/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (143695035451/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1441941941/10000000000:ℝ) + taylorErr ≤ (143695035451/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-198241936121/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-197924403039/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-143695035451/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-132300313531/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9557467298921/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9568972154831/1000000000000:ℝ) := by nlinarith
  have hp1 : (15817594821491/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15836635554133/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-142227869211/62500000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2092672754189/1000000000000:ℝ) := by nlinarith
  have hN : (68841442099/62500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (182130456199863/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (68841442099/62500000000:ℝ) (182130456199863/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (365741913/10000000000000:ℝ) ≤ ((68841442099/62500000000:ℝ)/(182130456199863/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_560 (x : ℝ) (h₁ : (6233/2048:ℝ) ≤ x) (h₂ : x ≤ (6243/2048:ℝ)) : (406405247/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1365242901/10000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (1518640981/10000000000:ℝ) := by nlinarith
  have hc1 : (61780674411/62500000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (61780674411/62500000000:ℝ) ≤ taylorCos (1518640981/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (247673756927/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1365242901/10000000000:ℝ) + taylorErr ≤ (247673756927/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (34025143223/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (34025143223/250000000000:ℝ) ≤ taylorSin (1365242901/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (75640520159/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1518640981/10000000000:ℝ) + taylorErr ≤ (75640520159/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-247673756927/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-61780674411/62500000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-75640520159/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-34025143223/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9561302250891/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9576642058771/1000000000000:ℝ) := by nlinarith
  have hp1 : (15823941661561/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3962332308611/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-239770301493/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-538411881387/250000000000:ℝ) := by nlinarith
  have hN : (14536906223/12500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (45606036560911/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (14536906223/12500000000:ℝ) (45606036560911/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (406405247/10000000000000:ℝ) ≤ ((14536906223/12500000000:ℝ)/(45606036560911/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_561 (x : ℝ) (h₁ : (6233/2048:ℝ) ≤ x) (h₂ : x ≤ (781/256:ℝ)) : (405098789/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1365242901/10000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (79767001/500000000:ℝ) := by nlinarith
  have hc1 : (493650707943/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (493650707943/500000000000:ℝ) ≤ taylorCos (79767001/500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (247673756927/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1365242901/10000000000:ℝ) + taylorErr ≤ (247673756927/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (34025143223/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (34025143223/250000000000:ℝ) ≤ taylorSin (1365242901/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-247673756927/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-493650707943/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-31771629131/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-34025143223/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9561302250891/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (958431196271/100000000000:ℝ) := by nlinarith
  have hp1 : (15823941661561/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (247844108043/15625000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-100792461863/40000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-538411881387/250000000000:ℝ) := by nlinarith
  have hN : (14536906223/12500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (182718071597093/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (14536906223/12500000000:ℝ) (182718071597093/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (405098789/10000000000000:ℝ) ≤ ((14536906223/12500000000:ℝ)/(182718071597093/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_562 (x : ℝ) (h₁ : (3119/1024:ℝ) ≤ x) (h₂ : x ≤ (781/256:ℝ)) : (495376037/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (72097097/500000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (79767001/500000000:ℝ) := by nlinarith
  have hc1 : (493650707943/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (493650707943/500000000000:ℝ) ≤ taylorCos (79767001/500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (494811009867/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (72097097/500000000:ℝ) + taylorErr ≤ (494811009867/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (35923757707/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (35923757707/250000000000:ℝ) ≤ taylorSin (72097097/500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-494811009867/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-493650707943/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-31771629131/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-35923757707/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (956897215483/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (958431196271/100000000000:ℝ) := by nlinarith
  have hp1 : (15836635341699/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (247844108043/15625000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-100792461863/40000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2275645803637/1000000000000:ℝ) := by nlinarith
  have hN : (1286023783903/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (182718071597093/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1286023783903/1000000000000:ℝ) (182718071597093/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (495376037/10000000000000:ℝ) ≤ ((1286023783903/1000000000000:ℝ)/(182718071597093/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_563 (x : ℝ) (h₁ : (3119/1024:ℝ) ≤ x) (h₂ : x ≤ (6253/2048:ℝ)) : (493784853/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (72097097/500000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (1672039059/10000000000:ℝ) := by nlinarith
  have hc1 : (986053961081/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (986053961081/1000000000000:ℝ) ≤ taylorCos (1672039059/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (494811009867/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (72097097/500000000:ℝ) + taylorErr ≤ (494811009867/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (35923757707/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (35923757707/250000000000:ℝ) ≤ taylorSin (72097097/500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (166425905823/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1672039059/10000000000:ℝ) + taylorErr ≤ (166425905823/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-494811009867/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-986053961081/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-166425905823/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-35923757707/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (956897215483/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9591981866649/1000000000000:ℝ) := by nlinarith
  have hp1 : (15836635341699/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15874716595061/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2641964089017/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2275645803637/1000000000000:ℝ) := by nlinarith
  have hN : (1286023783903/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (183012232260247/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1286023783903/1000000000000:ℝ) (183012232260247/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (493784853/10000000000000:ℝ) ≤ ((1286023783903/1000000000000:ℝ)/(183012232260247/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_564 (x : ℝ) (h₁ : (3119/1024:ℝ) ≤ x) (h₂ : x ≤ (3129/1024:ℝ)) : (24610003/500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (72097097/500000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (1748738099/10000000000:ℝ) := by nlinarith
  have hc1 : (492374249763/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (492374249763/500000000000:ℝ) ≤ taylorCos (1748738099/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (494811009867/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (72097097/500000000:ℝ) + taylorErr ≤ (494811009867/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (35923757707/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (35923757707/250000000000:ℝ) ≤ taylorSin (72097097/500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (173983875729/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1748738099/10000000000:ℝ) + taylorErr ≤ (173983875729/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-494811009867/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-492374249763/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-173983875729/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-35923757707/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (956897215483/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9599651770589/1000000000000:ℝ) := by nlinarith
  have hp1 : (15836635341699/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3971852568843/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1382076607503/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2275645803637/1000000000000:ℝ) := by nlinarith
  have hN : (1286023783903/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (91653314116573/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1286023783903/1000000000000:ℝ) (91653314116573/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (24610003/500000000000:ℝ) ≤ ((1286023783903/1000000000000:ℝ)/(91653314116573/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_565 (x : ℝ) (h₁ : (3119/1024:ℝ) ≤ x) (h₂ : x ≤ (1567/512:ℝ)) : (489049523/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (72097097/500000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (1902136177/10000000000:ℝ) := by nlinarith
  have hc1 : (981963866847/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (981963866847/1000000000000:ℝ) ≤ taylorCos (1902136177/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (494811009867/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (72097097/500000000:ℝ) + taylorErr ≤ (494811009867/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (35923757707/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (35923757707/250000000000:ℝ) ≤ taylorSin (72097097/500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (94534333207/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1902136177/10000000000:ℝ) + taylorErr ≤ (94534333207/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-494811009867/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-981963866847/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-94534333207/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-35923757707/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (956897215483/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2403747894617/250000000000:ℝ) := by nlinarith
  have hp1 : (15836635341699/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15912797635991/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-3008611427953/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2275645803637/1000000000000:ℝ) := by nlinarith
  have hN : (1286023783903/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (91948063054011/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1286023783903/1000000000000:ℝ) (91948063054011/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (489049523/10000000000000:ℝ) ≤ ((1286023783903/1000000000000:ℝ)/(91948063054011/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_566 (x : ℝ) (h₁ : (6243/2048:ℝ) ≤ x) (h₂ : x ≤ (6253/2048:ℝ)) : (148228771/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (75932049/500000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (1672039059/10000000000:ℝ) := by nlinarith
  have hc1 : (986053961081/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (986053961081/1000000000000:ℝ) ≤ taylorCos (1672039059/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (197698159023/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (75932049/500000000:ℝ) + taylorErr ≤ (197698159023/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (30256207139/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (30256207139/200000000000:ℝ) ≤ taylorSin (75932049/500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (166425905823/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1672039059/10000000000:ℝ) + taylorErr ≤ (166425905823/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-197698159023/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-986053961081/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-166425905823/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-30256207139/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (957664205877/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9591981866649/1000000000000:ℝ) := by nlinarith
  have hp1 : (15849329021839/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15874716595061/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2641964089017/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1198851454747/500000000000:ℝ) := by nlinarith
  have hN : (1409212114379/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (183012232260247/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1409212114379/1000000000000:ℝ) (183012232260247/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (148228771/2500000000000:ℝ) ≤ ((1409212114379/1000000000000:ℝ)/(183012232260247/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_567 (x : ℝ) (h₁ : (6243/2048:ℝ) ≤ x) (h₂ : x ≤ (3129/1024:ℝ)) : (295506067/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (75932049/500000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (1748738099/10000000000:ℝ) := by nlinarith
  have hc1 : (492374249763/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (492374249763/500000000000:ℝ) ≤ taylorCos (1748738099/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (197698159023/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (75932049/500000000:ℝ) + taylorErr ≤ (197698159023/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (30256207139/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (30256207139/200000000000:ℝ) ≤ taylorSin (75932049/500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (173983875729/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1748738099/10000000000:ℝ) + taylorErr ≤ (173983875729/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-197698159023/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-492374249763/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-173983875729/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-30256207139/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (957664205877/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9599651770589/1000000000000:ℝ) := by nlinarith
  have hp1 : (15849329021839/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3971852568843/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1382076607503/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1198851454747/500000000000:ℝ) := by nlinarith
  have hN : (1409212114379/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (91653314116573/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1409212114379/1000000000000:ℝ) (91653314116573/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (295506067/5000000000000:ℝ) ≤ ((1409212114379/1000000000000:ℝ)/(91653314116573/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_568 (x : ℝ) (h₁ : (781/256:ℝ) ≤ x) (h₂ : x ≤ (3129/1024:ℝ)) : (139791351/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1595340019/10000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (1748738099/10000000000:ℝ) := by nlinarith
  have hc1 : (492374249763/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (492374249763/500000000000:ℝ) ≤ taylorCos (1748738099/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (493650710213/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1595340019/10000000000:ℝ) + taylorErr ≤ (493650710213/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (19857267629/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (19857267629/125000000000:ℝ) ≤ taylorSin (1595340019/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (173983875729/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1748738099/10000000000:ℝ) + taylorErr ≤ (173983875729/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-493650710213/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-492374249763/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-173983875729/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-19857267629/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9584311962709/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9599651770589/1000000000000:ℝ) := by nlinarith
  have hp1 : (7931011350989/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3971852568843/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1382076607503/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2519811439443/1000000000000:ℝ) := by nlinarith
  have hN : (1532510019017/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (91653314116573/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1532510019017/1000000000000:ℝ) (91653314116573/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (139791351/2000000000000:ℝ) ≤ ((1532510019017/1000000000000:ℝ)/(91653314116573/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_569 (x : ℝ) (h₁ : (781/256:ℝ) ≤ x) (h₂ : x ≤ (6263/2048:ℝ)) : (27868611/400000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1595340019/10000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (912718569/5000000000:ℝ) := by nlinarith
  have hc1 : (245846277013/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (245846277013/250000000000:ℝ) ≤ taylorCos (912718569/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (493650710213/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1595340019/10000000000:ℝ) + taylorErr ≤ (493650710213/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (19857267629/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (19857267629/125000000000:ℝ) ≤ taylorSin (1595340019/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (45382902641/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (912718569/5000000000:ℝ) + taylorErr ≤ (45382902641/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-493650710213/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-245846277013/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-45382902641/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-19857267629/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9584311962709/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (300228802329/31250000000:ℝ) := by nlinarith
  have hp1 : (7931011350989/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (99375649723/6250000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-288637147921/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2519811439443/1000000000000:ℝ) := by nlinarith
  have hN : (1532510019017/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (183601259515711/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1532510019017/1000000000000:ℝ) (183601259515711/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (27868611/400000000000:ℝ) ≤ ((1532510019017/1000000000000:ℝ)/(183601259515711/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_570 (x : ℝ) (h₁ : (781/256:ℝ) ≤ x) (h₂ : x ≤ (1567/512:ℝ)) : (694482783/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1595340019/10000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (1902136177/10000000000:ℝ) := by nlinarith
  have hc1 : (981963866847/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (981963866847/1000000000000:ℝ) ≤ taylorCos (1902136177/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (493650710213/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1595340019/10000000000:ℝ) + taylorErr ≤ (493650710213/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (19857267629/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (19857267629/125000000000:ℝ) ≤ taylorSin (1595340019/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (94534333207/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1902136177/10000000000:ℝ) + taylorErr ≤ (94534333207/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-493650710213/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-981963866847/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-94534333207/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-19857267629/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9584311962709/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2403747894617/250000000000:ℝ) := by nlinarith
  have hp1 : (7931011350989/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15912797635991/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-3008611427953/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2519811439443/1000000000000:ℝ) := by nlinarith
  have hN : (1532510019017/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (91948063054011/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1532510019017/1000000000000:ℝ) (91948063054011/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (694482783/10000000000000:ℝ) ≤ ((1532510019017/1000000000000:ℝ)/(91948063054011/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_571 (x : ℝ) (h₁ : (781/256:ℝ) ≤ x) (h₂ : x ≤ (3139/1024:ℝ)) : (172511147/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1595340019/10000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (128470891/625000000:ℝ) := by nlinarith
  have hc1 : (244737043263/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (244737043263/250000000000:ℝ) ≤ taylorCos (128470891/625000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (493650710213/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1595340019/10000000000:ℝ) + taylorErr ≤ (493650710213/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (19857267629/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (19857267629/125000000000:ℝ) ≤ taylorSin (1595340019/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (102054484189/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (128470891/625000000:ℝ) + taylorErr ≤ (102054484189/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-493650710213/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-244737043263/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-102054484189/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-19857267629/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9584311962709/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9630331386347/1000000000000:ℝ) := by nlinarith
  have hp1 : (7931011350989/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1593818499661/100000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-813281624369/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2519811439443/1000000000000:ℝ) := by nlinarith
  have hN : (1532510019017/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (184486565221721/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1532510019017/1000000000000:ℝ) (184486565221721/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (172511147/2500000000000:ℝ) ≤ ((1532510019017/1000000000000:ℝ)/(184486565221721/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_572 (x : ℝ) (h₁ : (781/256:ℝ) ≤ x) (h₂ : x ≤ (393/128:ℝ)) : (685641829/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1595340019/10000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (441786467/2000000000:ℝ) := by nlinarith
  have hc1 : (975702127767/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (975702127767/1000000000000:ℝ) ≤ taylorCos (441786467/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (493650710213/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1595340019/10000000000:ℝ) + taylorErr ≤ (493650710213/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (19857267629/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (19857267629/125000000000:ℝ) ≤ taylorSin (1595340019/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (109550621231/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (441786467/2000000000:ℝ) + taylorErr ≤ (109550621231/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-493650710213/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-975702127767/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-109550621231/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-19857267629/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9584311962709/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (385826847769/40000000000:ℝ) := by nlinarith
  have hp1 : (7931011350989/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3990893089307/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-3497638537601/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2519811439443/1000000000000:ℝ) := by nlinarith
  have hN : (1532510019017/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (46269486393551/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1532510019017/1000000000000:ℝ) (46269486393551/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (685641829/10000000000000:ℝ) ≤ ((1532510019017/1000000000000:ℝ)/(46269486393551/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_573 (x : ℝ) (h₁ : (781/256:ℝ) ≤ x) (h₂ : x ≤ (1577/512:ℝ)) : (676941261/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1595340019/10000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (2515728493/10000000000:ℝ) := by nlinarith
  have hc1 : (968522091991/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (968522091991/1000000000000:ℝ) ≤ taylorCos (2515728493/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (493650710213/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1595340019/10000000000:ℝ) + taylorErr ≤ (493650710213/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (19857267629/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (19857267629/125000000000:ℝ) ≤ taylorSin (1595340019/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (62231902023/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2515728493/10000000000:ℝ) + taylorErr ≤ (62231902023/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-493650710213/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-968522091991/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-62231902023/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-19857267629/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9584311962709/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9676350809983/1000000000000:ℝ) := by nlinarith
  have hp1 : (7931011350989/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (8007173539233/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1993206556699/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2519811439443/1000000000000:ℝ) := by nlinarith
  have hN : (1532510019017/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (93131764997859/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1532510019017/1000000000000:ℝ) (93131764997859/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (676941261/10000000000000:ℝ) ≤ ((1532510019017/1000000000000:ℝ)/(93131764997859/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_574 (x : ℝ) (h₁ : (781/256:ℝ) ≤ x) (h₂ : x ≤ (791/256:ℝ)) : (66837841/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1595340019/10000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (56450493/200000000:ℝ) := by nlinarith
  have hc1 : (192086103429/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (192086103429/200000000000:ℝ) ≤ taylorCos (56450493/200000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (493650710213/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1595340019/10000000000:ℝ) + taylorErr ≤ (493650710213/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (19857267629/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (19857267629/125000000000:ℝ) ≤ taylorSin (1595340019/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (11140787667/40000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (56450493/200000000:ℝ) + taylorErr ≤ (11140787667/40000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-493650710213/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-192086103429/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-11140787667/40000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-19857267629/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9584311962709/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9707030425741/1000000000000:ℝ) := by nlinarith
  have hp1 : (7931011350989/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3213024359941/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-559306596297/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2519811439443/1000000000000:ℝ) := by nlinarith
  have hN : (1532510019017/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (187452879372523/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1532510019017/1000000000000:ℝ) (187452879372523/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (66837841/1000000000000:ℝ) ≤ ((1532510019017/1000000000000:ℝ)/(187452879372523/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_575 (x : ℝ) (h₁ : (781/256:ℝ) ≤ x) (h₂ : x ≤ (1587/512:ℝ)) : (329975333/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1595340019/10000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (391165101/1250000000:ℝ) := by nlinarith
  have hc1 : (190287003737/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (190287003737/200000000000:ℝ) ≤ taylorCos (391165101/1250000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (493650710213/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1595340019/10000000000:ℝ) + taylorErr ≤ (493650710213/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (19857267629/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (19857267629/125000000000:ℝ) ≤ taylorSin (1595340019/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (76962410593/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (391165101/1250000000:ℝ) + taylorErr ≤ (76962410593/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-493650710213/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-190287003737/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-76962410593/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-19857267629/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9584311962709/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9737710041499/1000000000000:ℝ) := by nlinarith
  have hp1 : (7931011350989/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (16115896520943/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-4961272980477/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2519811439443/1000000000000:ℝ) := by nlinarith
  have hN : (1532510019017/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (188645993704621/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1532510019017/1000000000000:ℝ) (188645993704621/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (329975333/5000000000000:ℝ) ≤ ((1532510019017/1000000000000:ℝ)/(188645993704621/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_576 (x : ℝ) (h₁ : (781/256:ℝ) ≤ x) (h₂ : x ≤ (199/64:ℝ)) : (162913869/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1595340019/10000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (687223393/2000000000:ℝ) := by nlinarith
  have hc1 : (235386015729/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (235386015729/250000000000:ℝ) ≤ taylorCos (687223393/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (493650710213/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1595340019/10000000000:ℝ) + taylorErr ≤ (493650710213/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (19857267629/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (19857267629/125000000000:ℝ) ≤ taylorSin (1595340019/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (336889855667/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (687223393/2000000000:ℝ) + taylorErr ≤ (336889855667/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-493650710213/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-235386015729/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-336889855667/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-19857267629/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9584311962709/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1221048707157/125000000000:ℝ) := by nlinarith
  have hp1 : (7931011350989/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (808333562109/50000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2723193770697/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2519811439443/1000000000000:ℝ) := by nlinarith
  have hN : (1532510019017/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (47460718247993/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1532510019017/1000000000000:ℝ) (47460718247993/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (162913869/2500000000000:ℝ) ≤ ((1532510019017/1000000000000:ℝ)/(47460718247993/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_577 (x : ℝ) (h₁ : (781/256:ℝ) ≤ x) (h₂ : x ≤ (801/256:ℝ)) : (635452827/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1595340019/10000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (4049709281/10000000000:ℝ) := by nlinarith
  have hc1 : (919113849389/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (919113849389/1000000000000:ℝ) ≤ taylorCos (4049709281/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (493650710213/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1595340019/10000000000:ℝ) + taylorErr ≤ (493650710213/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (19857267629/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (19857267629/125000000000:ℝ) ≤ taylorSin (1595340019/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (393992042413/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (4049709281/10000000000:ℝ) + taylorErr ≤ (393992042413/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-493650710213/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-919113849389/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-393992042413/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-19857267629/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9584311962709/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2457437222193/250000000000:ℝ) := by nlinarith
  have hp1 : (7931011350989/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (16268220684657/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-3204774746987/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2519811439443/1000000000000:ℝ) := by nlinarith
  have hN : (1532510019017/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (192247926432629/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1532510019017/1000000000000:ℝ) (192247926432629/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (635452827/10000000000000:ℝ) ≤ ((1532510019017/1000000000000:ℝ)/(192247926432629/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_578 (x : ℝ) (h₁ : (6253/2048:ℝ) ≤ x) (h₂ : x ≤ (6263/2048:ℝ)) : (162686737/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (836019529/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (912718569/5000000000:ℝ) := by nlinarith
  have hc1 : (245846277013/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (245846277013/250000000000:ℝ) ≤ taylorCos (912718569/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (493026982811/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (836019529/5000000000:ℝ) + taylorErr ≤ (493026982811/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (416064753/2500000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (416064753/2500000000:ℝ) ≤ taylorSin (836019529/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (45382902641/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (912718569/5000000000:ℝ) + taylorErr ≤ (45382902641/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-493026982811/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-245846277013/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-45382902641/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-416064753/2500000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1198997733331/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (300228802329/31250000000:ℝ) := by nlinarith
  have hp1 : (3968679095529/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (99375649723/6250000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-288637147921/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-660490995047/250000000000:ℝ) := by nlinarith
  have hN : (827955007283/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (183601259515711/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (827955007283/500000000000:ℝ) (183601259515711/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (162686737/2000000000000:ℝ) ≤ ((827955007283/500000000000:ℝ)/(183601259515711/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_579 (x : ℝ) (h₁ : (6253/2048:ℝ) ≤ x) (h₂ : x ≤ (1567/512:ℝ)) : (81082719/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (836019529/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (1902136177/10000000000:ℝ) := by nlinarith
  have hc1 : (981963866847/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (981963866847/1000000000000:ℝ) ≤ taylorCos (1902136177/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (493026982811/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (836019529/5000000000:ℝ) + taylorErr ≤ (493026982811/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (416064753/2500000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (416064753/2500000000:ℝ) ≤ taylorSin (836019529/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (94534333207/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1902136177/10000000000:ℝ) + taylorErr ≤ (94534333207/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-493026982811/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-981963866847/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-94534333207/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-416064753/2500000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1198997733331/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2403747894617/250000000000:ℝ) := by nlinarith
  have hp1 : (3968679095529/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15912797635991/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-3008611427953/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-660490995047/250000000000:ℝ) := by nlinarith
  have hN : (827955007283/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (91948063054011/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (827955007283/500000000000:ℝ) (91948063054011/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (81082719/1000000000000:ℝ) ≤ ((827955007283/500000000000:ℝ)/(91948063054011/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_580 (x : ℝ) (h₁ : (3129/1024:ℝ) ≤ x) (h₂ : x ≤ (3139/1024:ℝ)) : (930293373/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (874369049/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (128470891/625000000:ℝ) := by nlinarith
  have hc1 : (244737043263/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (244737043263/250000000000:ℝ) ≤ taylorCos (128470891/625000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (984748504067/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (874369049/5000000000:ℝ) + taylorErr ≤ (984748504067/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (173983871107/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (173983871107/1000000000000:ℝ) ≤ taylorSin (874369049/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (102054484189/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (128470891/625000000:ℝ) + taylorErr ≤ (102054484189/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-984748504067/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-244737043263/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-102054484189/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-173983871107/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (2399912942647/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9630331386347/1000000000000:ℝ) := by nlinarith
  have hp1 : (15887410062257/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1593818499661/100000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-813281624369/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-552830620899/200000000000:ℝ) := by nlinarith
  have hN : (444851150107/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (184486565221721/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (444851150107/250000000000:ℝ) (184486565221721/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (930293373/10000000000000:ℝ) ≤ ((444851150107/250000000000:ℝ)/(184486565221721/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_581 (x : ℝ) (h₁ : (3129/1024:ℝ) ≤ x) (h₂ : x ≤ (393/128:ℝ)) : (924357731/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (874369049/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (441786467/2000000000:ℝ) := by nlinarith
  have hc1 : (975702127767/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (975702127767/1000000000000:ℝ) ≤ taylorCos (441786467/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (984748504067/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (874369049/5000000000:ℝ) + taylorErr ≤ (984748504067/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (173983871107/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (173983871107/1000000000000:ℝ) ≤ taylorSin (874369049/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (109550621231/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (441786467/2000000000:ℝ) + taylorErr ≤ (109550621231/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-984748504067/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-975702127767/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-109550621231/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-173983871107/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (2399912942647/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (385826847769/40000000000:ℝ) := by nlinarith
  have hp1 : (15887410062257/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3990893089307/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-3497638537601/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-552830620899/200000000000:ℝ) := by nlinarith
  have hN : (444851150107/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (46269486393551/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (444851150107/250000000000:ℝ) (46269486393551/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (924357731/10000000000000:ℝ) ≤ ((444851150107/250000000000:ℝ)/(46269486393551/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_582 (x : ℝ) (h₁ : (1567/512:ℝ) ≤ x) (h₂ : x ≤ (393/128:ℝ)) : (9367789/78125000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (118883511/625000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (441786467/2000000000:ℝ) := by nlinarith
  have hc1 : (975702127767/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (975702127767/1000000000000:ℝ) ≤ taylorCos (441786467/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (98196387139/100000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (118883511/625000000:ℝ) + taylorErr ≤ (98196387139/100000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (5908395681/31250000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (5908395681/31250000000:ℝ) ≤ taylorSin (118883511/625000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (109550621231/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (441786467/2000000000:ℝ) + taylorErr ≤ (109550621231/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-98196387139/100000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-975702127767/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-109550621231/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-5908395681/31250000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9614991578467/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (385826847769/40000000000:ℝ) := by nlinarith
  have hp1 : (3182559484507/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3990893089307/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-3497638537601/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-601722262809/200000000000:ℝ) := by nlinarith
  have hN : (405329488531/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (46269486393551/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (405329488531/200000000000:ℝ) (46269486393551/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (9367789/78125000000:ℝ) ≤ ((405329488531/200000000000:ℝ)/(46269486393551/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_583 (x : ℝ) (h₁ : (1567/512:ℝ) ≤ x) (h₂ : x ≤ (3149/1024:ℝ)) : (297859663/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (118883511/625000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (1181165207/5000000000:ℝ) := by nlinarith
  have hc1 : (972226494801/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (972226494801/1000000000000:ℝ) ≤ taylorCos (1181165207/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (98196387139/100000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (118883511/625000000:ℝ) + taylorErr ≤ (98196387139/100000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (5908395681/31250000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (5908395681/31250000000:ℝ) ≤ taylorSin (118883511/625000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (234041960909/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1181165207/5000000000:ℝ) + taylorErr ≤ (234041960909/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-98196387139/100000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-972226494801/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-234041960909/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-5908395681/31250000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9614991578467/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1207626375263/125000000000:ℝ) := by nlinarith
  have hp1 : (3182559484507/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15988959717847/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-187104374263/50000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-601722262809/200000000000:ℝ) := by nlinarith
  have hN : (405329488531/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (3713405343311/20000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (405329488531/200000000000:ℝ) (3713405343311/20000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (297859663/2500000000000:ℝ) ≤ ((405329488531/200000000000:ℝ)/(3713405343311/20000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_584 (x : ℝ) (h₁ : (1567/512:ℝ) ≤ x) (h₂ : x ≤ (1577/512:ℝ)) : (591930551/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (118883511/625000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (2515728493/10000000000:ℝ) := by nlinarith
  have hc1 : (968522091991/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (968522091991/1000000000000:ℝ) ≤ taylorCos (2515728493/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (98196387139/100000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (118883511/625000000:ℝ) + taylorErr ≤ (98196387139/100000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (5908395681/31250000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (5908395681/31250000000:ℝ) ≤ taylorSin (118883511/625000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (62231902023/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2515728493/10000000000:ℝ) + taylorErr ≤ (62231902023/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-98196387139/100000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-968522091991/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-62231902023/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-5908395681/31250000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9614991578467/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9676350809983/1000000000000:ℝ) := by nlinarith
  have hp1 : (3182559484507/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (8007173539233/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1993206556699/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-601722262809/200000000000:ℝ) := by nlinarith
  have hN : (405329488531/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (93131764997859/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (405329488531/200000000000:ℝ) (93131764997859/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (591930551/5000000000000:ℝ) ≤ ((405329488531/200000000000:ℝ)/(93131764997859/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_585 (x : ℝ) (h₁ : (1567/512:ℝ) ≤ x) (h₂ : x ≤ (791/256:ℝ)) : (1168886057/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (118883511/625000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (56450493/200000000:ℝ) := by nlinarith
  have hc1 : (192086103429/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (192086103429/200000000000:ℝ) ≤ taylorCos (56450493/200000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (98196387139/100000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (118883511/625000000:ℝ) + taylorErr ≤ (98196387139/100000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (5908395681/31250000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (5908395681/31250000000:ℝ) ≤ taylorSin (118883511/625000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (11140787667/40000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (56450493/200000000:ℝ) + taylorErr ≤ (11140787667/40000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-98196387139/100000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-192086103429/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-11140787667/40000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-5908395681/31250000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9614991578467/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9707030425741/1000000000000:ℝ) := by nlinarith
  have hp1 : (3182559484507/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3213024359941/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-559306596297/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-601722262809/200000000000:ℝ) := by nlinarith
  have hN : (405329488531/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (187452879372523/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (405329488531/200000000000:ℝ) (187452879372523/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1168886057/10000000000000:ℝ) ≤ ((405329488531/200000000000:ℝ)/(187452879372523/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_586 (x : ℝ) (h₁ : (1567/512:ℝ) ≤ x) (h₂ : x ≤ (1587/512:ℝ)) : (288536823/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (118883511/625000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (391165101/1250000000:ℝ) := by nlinarith
  have hc1 : (190287003737/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (190287003737/200000000000:ℝ) ≤ taylorCos (391165101/1250000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (98196387139/100000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (118883511/625000000:ℝ) + taylorErr ≤ (98196387139/100000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (5908395681/31250000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (5908395681/31250000000:ℝ) ≤ taylorSin (118883511/625000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (76962410593/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (391165101/1250000000:ℝ) + taylorErr ≤ (76962410593/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-98196387139/100000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-190287003737/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-76962410593/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-5908395681/31250000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9614991578467/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9737710041499/1000000000000:ℝ) := by nlinarith
  have hp1 : (3182559484507/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (16115896520943/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-4961272980477/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-601722262809/200000000000:ℝ) := by nlinarith
  have hN : (405329488531/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (188645993704621/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (405329488531/200000000000:ℝ) (188645993704621/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (288536823/2500000000000:ℝ) ≤ ((405329488531/200000000000:ℝ)/(188645993704621/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_587 (x : ℝ) (h₁ : (1567/512:ℝ) ≤ x) (h₂ : x ≤ (199/64:ℝ)) : (569820171/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (118883511/625000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (687223393/2000000000:ℝ) := by nlinarith
  have hc1 : (235386015729/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (235386015729/250000000000:ℝ) ≤ taylorCos (687223393/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (98196387139/100000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (118883511/625000000:ℝ) + taylorErr ≤ (98196387139/100000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (5908395681/31250000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (5908395681/31250000000:ℝ) ≤ taylorSin (118883511/625000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (336889855667/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (687223393/2000000000:ℝ) + taylorErr ≤ (336889855667/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-98196387139/100000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-235386015729/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-336889855667/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-5908395681/31250000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9614991578467/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1221048707157/125000000000:ℝ) := by nlinarith
  have hp1 : (3182559484507/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (808333562109/50000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2723193770697/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-601722262809/200000000000:ℝ) := by nlinarith
  have hN : (405329488531/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (47460718247993/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (405329488531/200000000000:ℝ) (47460718247993/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (569820171/5000000000000:ℝ) ≤ ((405329488531/200000000000:ℝ)/(47460718247993/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_588 (x : ℝ) (h₁ : (3139/1024:ℝ) ≤ x) (h₂ : x ≤ (1577/512:ℝ)) : (298142111/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (411106851/2000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (2515728493/10000000000:ℝ) := by nlinarith
  have hc1 : (968522091991/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (968522091991/1000000000000:ℝ) ≤ taylorCos (2515728493/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (978948177597/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (411106851/2000000000:ℝ) + taylorErr ≤ (978948177597/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (51027240939/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (51027240939/250000000000:ℝ) ≤ taylorSin (411106851/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (62231902023/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2515728493/10000000000:ℝ) + taylorErr ≤ (62231902023/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-978948177597/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-968522091991/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-62231902023/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-51027240939/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (4815165693173/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9676350809983/1000000000000:ℝ) := by nlinarith
  have hp1 : (7969092391407/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (8007173539233/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1993206556699/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-3253126380171/1000000000000:ℝ) := by nlinarith
  have hN : (1137089101287/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (93131764997859/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1137089101287/500000000000:ℝ) (93131764997859/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (298142111/2000000000000:ℝ) ≤ ((1137089101287/500000000000:ℝ)/(93131764997859/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_589 (x : ℝ) (h₁ : (393/128:ℝ) ≤ x) (h₂ : x ≤ (791/256:ℝ)) : (1810022563/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1104466167/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (56450493/200000000:ℝ) := by nlinarith
  have hc1 : (192086103429/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (192086103429/200000000000:ℝ) ≤ taylorCos (56450493/200000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (975702132313/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1104466167/5000000000:ℝ) + taylorErr ≤ (975702132313/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (219101237841/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (219101237841/1000000000000:ℝ) ≤ taylorSin (1104466167/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (11140787667/40000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (56450493/200000000:ℝ) + taylorErr ≤ (11140787667/40000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-975702132313/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-192086103429/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-11140787667/40000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-219101237841/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (602854449639/62500000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9707030425741/1000000000000:ℝ) := by nlinarith
  have hp1 : (15963572143091/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3213024359941/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-559306596297/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-699527683383/200000000000:ℝ) := by nlinarith
  have hN : (1260968142301/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (187452879372523/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1260968142301/500000000000:ℝ) (187452879372523/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1810022563/10000000000000:ℝ) ≤ ((1260968142301/500000000000:ℝ)/(187452879372523/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_590 (x : ℝ) (h₁ : (393/128:ℝ) ≤ x) (h₂ : x ≤ (199/64:ℝ)) : (1764735511/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1104466167/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (687223393/2000000000:ℝ) := by nlinarith
  have hc1 : (235386015729/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (235386015729/250000000000:ℝ) ≤ taylorCos (687223393/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (975702132313/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1104466167/5000000000:ℝ) + taylorErr ≤ (975702132313/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (219101237841/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (219101237841/1000000000000:ℝ) ≤ taylorSin (1104466167/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (336889855667/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (687223393/2000000000:ℝ) + taylorErr ≤ (336889855667/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-975702132313/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-235386015729/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-336889855667/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-219101237841/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (602854449639/62500000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1221048707157/125000000000:ℝ) := by nlinarith
  have hp1 : (15963572143091/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (808333562109/50000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2723193770697/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-699527683383/200000000000:ℝ) := by nlinarith
  have hN : (1260968142301/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (47460718247993/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1260968142301/500000000000:ℝ) (47460718247993/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1764735511/10000000000000:ℝ) ≤ ((1260968142301/500000000000:ℝ)/(47460718247993/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_591 (x : ℝ) (h₁ : (393/128:ℝ) ≤ x) (h₂ : x ≤ (801/256:ℝ)) : (215107179/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1104466167/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (4049709281/10000000000:ℝ) := by nlinarith
  have hc1 : (919113849389/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (919113849389/1000000000000:ℝ) ≤ taylorCos (4049709281/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (975702132313/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1104466167/5000000000:ℝ) + taylorErr ≤ (975702132313/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (219101237841/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (219101237841/1000000000000:ℝ) ≤ taylorSin (1104466167/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (393992042413/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (4049709281/10000000000:ℝ) + taylorErr ≤ (393992042413/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-975702132313/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-919113849389/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-393992042413/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-219101237841/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (602854449639/62500000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2457437222193/250000000000:ℝ) := by nlinarith
  have hp1 : (15963572143091/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (16268220684657/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-3204774746987/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-699527683383/200000000000:ℝ) := by nlinarith
  have hN : (1260968142301/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (192247926432629/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1260968142301/500000000000:ℝ) (192247926432629/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (215107179/1250000000000:ℝ) ≤ ((1260968142301/500000000000:ℝ)/(192247926432629/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_592 (x : ℝ) (h₁ : (393/128:ℝ) ≤ x) (h₂ : x ≤ (403/128:ℝ)) : (419583999/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1104466167/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (1165825399/2500000000:ℝ) := by nlinarith
  have hc1 : (55826518681/62500000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (55826518681/62500000000:ℝ) ≤ taylorCos (1165825399/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (975702132313/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1104466167/5000000000:ℝ) + taylorErr ≤ (975702132313/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (219101237841/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (219101237841/1000000000000:ℝ) ≤ taylorSin (1104466167/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (449611331991/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1165825399/2500000000:ℝ) + taylorErr ≤ (449611331991/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-975702132313/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-55826518681/62500000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-449611331991/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-219101237841/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (602854449639/62500000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9891108120287/1000000000000:ℝ) := by nlinarith
  have hp1 : (15963572143091/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (4092442531783/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-7360034151247/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-699527683383/200000000000:ℝ) := by nlinarith
  have hN : (1260968142301/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (38933607938883/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1260968142301/500000000000:ℝ) (38933607938883/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (419583999/2500000000000:ℝ) ≤ ((1260968142301/500000000000:ℝ)/(38933607938883/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_593 (x : ℝ) (h₁ : (393/128:ℝ) ≤ x) (h₂ : x ≤ (811/256:ℝ)) : (1637121129/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1104466167/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (5276893911/10000000000:ℝ) := by nlinarith
  have hc1 : (34558914153/40000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (34558914153/40000000000:ℝ) ≤ taylorCos (5276893911/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (975702132313/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1104466167/5000000000:ℝ) + taylorErr ≤ (975702132313/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (219101237841/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (219101237841/1000000000000:ℝ) ≤ taylorSin (1104466167/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-975702132313/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-34558914153/40000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-251769193023/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-219101237841/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (602854449639/62500000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9952467351803/1000000000000:ℝ) := by nlinarith
  have hp1 : (15963572143091/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (16471319569609/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-8293941672129/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-699527683383/200000000000:ℝ) := by nlinarith
  have hN : (1260968142301/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (19710321277741/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1260968142301/500000000000:ℝ) (19710321277741/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1637121129/10000000000000:ℝ) ≤ ((1260968142301/500000000000:ℝ)/(19710321277741/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_594 (x : ℝ) (h₁ : (393/128:ℝ) ≤ x) (h₂ : x ≤ (51/16:ℝ)) : (798582451/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1104466167/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (2945243113/5000000000:ℝ) := by nlinarith
  have hc1 : (103933701251/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (103933701251/125000000000:ℝ) ≤ taylorCos (2945243113/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (975702132313/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1104466167/5000000000:ℝ) + taylorErr ≤ (975702132313/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (219101237841/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (219101237841/1000000000000:ℝ) ≤ taylorSin (1104466167/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-975702132313/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-103933701251/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-22222809413/40000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-219101237841/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (602854449639/62500000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (5006913291659/500000000000:ℝ) := by nlinarith
  have hp1 : (15963572143091/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (4143217253021/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-4603696368527/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-699527683383/200000000000:ℝ) := by nlinarith
  have hN : (1260968142301/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (199553445681533/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1260968142301/500000000000:ℝ) (199553445681533/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (798582451/5000000000000:ℝ) ≤ ((1260968142301/500000000000:ℝ)/(199553445681533/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_595 (x : ℝ) (h₁ : (393/128:ℝ) ≤ x) (h₂ : x ≤ (413/128:ℝ)) : (1520846759/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1104466167/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (889708857/1250000000:ℝ) := by nlinarith
  have hc1 : (151441768839/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (151441768839/200000000000:ℝ) ≤ taylorCos (889708857/1250000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (975702132313/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1104466167/5000000000:ℝ) + taylorErr ≤ (975702132313/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (219101237841/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (219101237841/1000000000000:ℝ) ≤ taylorSin (1104466167/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-975702132313/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-151441768839/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-65317284523/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-219101237841/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (602854449639/62500000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (10136545046349/1000000000000:ℝ) := by nlinarith
  have hp1 : (15963572143091/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (16775967897037/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2191521336559/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-699527683383/200000000000:ℝ) := by nlinarith
  have hN : (1260968142301/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (8179963638133/40000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1260968142301/500000000000:ℝ) (8179963638133/40000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1520846759/10000000000000:ℝ) ≤ ((1260968142301/500000000000:ℝ)/(8179963638133/40000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_596 (x : ℝ) (h₁ : (393/128:ℝ) ≤ x) (h₂ : x ≤ (13/4:ℝ)) : (1477240831/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1104466167/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (975702132313/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1104466167/5000000000:ℝ) + taylorErr ≤ (975702132313/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (219101237841/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (219101237841/1000000000000:ℝ) ≤ taylorSin (1104466167/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-975702132313/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-88388347351/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-176776695861/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-219101237841/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (602854449639/62500000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (10210176124167/1000000000000:ℝ) := by nlinarith
  have hp1 : (15963572143091/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (16897827228007/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-11948568258389/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-699527683383/200000000000:ℝ) := by nlinarith
  have hN : (1260968142301/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10374769648651/50000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1260968142301/500000000000:ℝ) (10374769648651/50000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1477240831/10000000000000:ℝ) ≤ ((1260968142301/500000000000:ℝ)/(10374769648651/50000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_597 (x : ℝ) (h₁ : (1577/512:ℝ) ≤ x) (h₂ : x ≤ (1597/512:ℝ)) : (124770657/500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (628932123/2500000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (3742913123/10000000000:ℝ) := by nlinarith
  have hc1 : (232691739699/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (232691739699/250000000000:ℝ) ≤ taylorCos (3742913123/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (48426104827/50000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (628932123/2500000000:ℝ) + taylorErr ≤ (48426104827/50000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (248927603471/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (248927603471/1000000000000:ℝ) ≤ taylorSin (628932123/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (365613000119/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3742913123/10000000000:ℝ) + taylorErr ≤ (365613000119/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-48426104827/50000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-232691739699/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-365613000119/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-248927603471/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (4838175404991/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (4899534636507/500000000000:ℝ) := by nlinarith
  have hp1 : (500448339489/31250000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (8108722981709/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2964654536477/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-3986412985921/1000000000000:ℝ) := by nlinarith
  have hN : (3017890889381/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (38208703446931/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3017890889381/1000000000000:ℝ) (38208703446931/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (124770657/500000000000:ℝ) ≤ ((3017890889381/1000000000000:ℝ)/(38208703446931/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_598 (x : ℝ) (h₁ : (791/256:ℝ) ≤ x) (h₂ : x ≤ (801/256:ℝ)) : (1670535297/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2822524649/10000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (4049709281/10000000000:ℝ) := by nlinarith
  have hc1 : (919113849389/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (919113849389/1000000000000:ℝ) ≤ taylorCos (4049709281/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (960430521697/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2822524649/10000000000:ℝ) + taylorErr ≤ (960430521697/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (55703937411/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (55703937411/200000000000:ℝ) ≤ taylorSin (2822524649/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (393992042413/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (4049709281/10000000000:ℝ) + taylorErr ≤ (393992042413/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (-919113849389/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-393992042413/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-55703937411/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (485351521287/50000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2457437222193/250000000000:ℝ) := by nlinarith
  have hp1 : (8032560792103/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (16268220684657/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-3204774746987/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-4474452636133/1000000000000:ℝ) := by nlinarith
  have hN : (878505528609/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (192247926432629/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (878505528609/250000000000:ℝ) (192247926432629/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1670535297/5000000000000:ℝ) ≤ ((878505528609/250000000000:ℝ)/(192247926432629/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_599 (x : ℝ) (h₁ : (791/256:ℝ) ≤ x) (h₂ : x ≤ (403/128:ℝ)) : (1629257293/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2822524649/10000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (1165825399/2500000000:ℝ) := by nlinarith
  have hc1 : (55826518681/62500000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (55826518681/62500000000:ℝ) ≤ taylorCos (1165825399/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (960430521697/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2822524649/10000000000:ℝ) + taylorErr ≤ (960430521697/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (55703937411/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (55703937411/200000000000:ℝ) ≤ taylorSin (2822524649/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (449611331991/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1165825399/2500000000:ℝ) + taylorErr ≤ (449611331991/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (-55826518681/62500000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-449611331991/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-55703937411/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (485351521287/50000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9891108120287/1000000000000:ℝ) := by nlinarith
  have hp1 : (8032560792103/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (4092442531783/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-7360034151247/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-4474452636133/1000000000000:ℝ) := by nlinarith
  have hN : (878505528609/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (38933607938883/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (878505528609/250000000000:ℝ) (38933607938883/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1629257293/5000000000000:ℝ) ≤ ((878505528609/250000000000:ℝ)/(38933607938883/200000000000:ℝ))^2 := by norm_num
  linarith

end Zeta23Ext.Bridge.FourPoint
