import ThreePoint.Base

noncomputable section
open Real
namespace Zeta23Ext.Bridge.ThreePoint


theorem wc_240 (x : ℝ) (h₁ : (12495/4096:ℝ) ≤ x) (h₂ : x ≤ (24999/8192:ℝ)) : (69140943/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (317534023/2000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (405546171/2500000000:ℝ) := by nlinarith
  have hc1 : (246717852407/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (246717852407/250000000000:ℝ) ≤ taylorCos (405546171/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (987422972683/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (317534023/2000000000:ℝ) + taylorErr ≤ (987422972683/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (158100843671/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (158100843671/1000000000000:ℝ) ≤ taylorSin (317534023/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (161507947561/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (405546171/2500000000:ℝ) + taylorErr ≤ (161507947561/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-987422972683/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-246717852407/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-161507947561/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-158100843671/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1916708994463/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9586996429089/1000000000000:ℝ) := by nlinarith
  have hp1 : (3965188333491/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15866465702861/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2562560310717/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2507598483357/1000000000000:ℝ) := by nlinarith
  have hN : (760087755337/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (182821001062731/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (760087755337/500000000000:ℝ) (182821001062731/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (69140943/1000000000000:ℝ) ≤ ((760087755337/500000000000:ℝ)/(182821001062731/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_241 (x : ℝ) (h₁ : (12495/4096:ℝ) ≤ x) (h₂ : x ≤ (12501/4096:ℝ)) : (27643033/400000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (317534023/2000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (81684477/500000000:ℝ) := by nlinarith
  have hc1 : (986684943983/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (986684943983/1000000000000:ℝ) ≤ taylorCos (81684477/500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (987422972683/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (317534023/2000000000:ℝ) + taylorErr ≤ (987422972683/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (158100843671/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (158100843671/1000000000000:ℝ) ≤ taylorSin (317534023/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (40660805443/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (81684477/500000000:ℝ) + taylorErr ≤ (40660805443/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-987422972683/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-986684943983/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-40660805443/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-158100843671/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1916708994463/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (239703672867/25000000000:ℝ) := by nlinarith
  have hp1 : (3965188333491/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3967092438727/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-322610347651/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2507598483357/1000000000000:ℝ) := by nlinarith
  have hN : (760087755337/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (5714535078593/31250000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (760087755337/500000000000:ℝ) (5714535078593/31250000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (27643033/400000000000:ℝ) ≤ ((760087755337/500000000000:ℝ)/(5714535078593/31250000000:ℝ))^2 := by norm_num
  linarith

theorem wc_242 (x : ℝ) (h₁ : (12495/4096:ℝ) ≤ x) (h₂ : x ≤ (1563/512:ℝ)) : (34520461/500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (317534023/2000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (1656699251/10000000000:ℝ) := by nlinarith
  have hc1 : (986308094981/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (986308094981/1000000000000:ℝ) ≤ taylorCos (1656699251/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (987422972683/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (317534023/2000000000:ℝ) + taylorErr ≤ (987422972683/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (158100843671/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (158100843671/1000000000000:ℝ) ≤ taylorSin (317534023/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (4122828069/25000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1656699251/10000000000:ℝ) + taylorErr ≤ (4122828069/25000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-987422972683/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-986308094981/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-4122828069/25000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-158100843671/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1916708994463/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (4795223942931/500000000000:ℝ) := by nlinarith
  have hp1 : (3965188333491/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15872177859001/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-261753041573/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2507598483357/1000000000000:ℝ) := by nlinarith
  have hN : (760087755337/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (18295338130287/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (760087755337/500000000000:ℝ) (18295338130287/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (34520461/500000000000:ℝ) ≤ ((760087755337/500000000000:ℝ)/(18295338130287/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_243 (x : ℝ) (h₁ : (24993/8192:ℝ) ≤ x) (h₂ : x ≤ (24999/8192:ℝ)) : (708342221/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1599174971/10000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (405546171/2500000000:ℝ) := by nlinarith
  have hc1 : (246717852407/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (246717852407/250000000000:ℝ) ≤ taylorCos (405546171/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (246810106623/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1599174971/10000000000:ℝ) + taylorErr ≤ (246810106623/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (19904594337/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (19904594337/125000000000:ℝ) ≤ taylorSin (1599174971/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (161507947561/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (405546171/2500000000:ℝ) + taylorErr ≤ (161507947561/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-246810106623/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-246717852407/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-161507947561/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-19904594337/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (4792347728953/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9586996429089/1000000000000:ℝ) := by nlinarith
  have hp1 : (3172531477197/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15866465702861/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2562560310717/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1262959041499/500000000000:ℝ) := by nlinarith
  have hN : (769338828253/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (182821001062731/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (769338828253/500000000000:ℝ) (182821001062731/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (708342221/10000000000000:ℝ) ≤ ((769338828253/500000000000:ℝ)/(182821001062731/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_244 (x : ℝ) (h₁ : (24993/8192:ℝ) ≤ x) (h₂ : x ≤ (12501/4096:ℝ)) : (708000447/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1599174971/10000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (81684477/500000000:ℝ) := by nlinarith
  have hc1 : (986684943983/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (986684943983/1000000000000:ℝ) ≤ taylorCos (81684477/500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (246810106623/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1599174971/10000000000:ℝ) + taylorErr ≤ (246810106623/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (19904594337/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (19904594337/125000000000:ℝ) ≤ taylorSin (1599174971/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (40660805443/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (81684477/500000000:ℝ) + taylorErr ≤ (40660805443/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-246810106623/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-986684943983/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-40660805443/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-19904594337/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (4792347728953/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (239703672867/25000000000:ℝ) := by nlinarith
  have hp1 : (3172531477197/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3967092438727/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-322610347651/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1262959041499/500000000000:ℝ) := by nlinarith
  have hN : (769338828253/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (5714535078593/31250000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (769338828253/500000000000:ℝ) (5714535078593/31250000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (708000447/10000000000000:ℝ) ≤ ((769338828253/500000000000:ℝ)/(5714535078593/31250000000:ℝ))^2 := by norm_num
  linarith

theorem wc_245 (x : ℝ) (h₁ : (6249/2048:ℝ) ≤ x) (h₂ : x ≤ (12501/4096:ℝ)) : (145026389/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1610679827/10000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (81684477/500000000:ℝ) := by nlinarith
  have hc1 : (986684943983/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (986684943983/1000000000000:ℝ) ≤ taylorCos (81684477/500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (246764143393/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1610679827/10000000000:ℝ) + taylorErr ≤ (246764143393/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (160372454953/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (160372454953/1000000000000:ℝ) ≤ taylorSin (1610679827/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (40660805443/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (81684477/500000000:ℝ) + taylorErr ≤ (40660805443/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-246764143393/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-986684943983/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-40660805443/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-160372454953/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9585845943497/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (239703672867/25000000000:ℝ) := by nlinarith
  have hp1 : (7932280719003/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3967092438727/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-322610347651/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-508847732913/200000000000:ℝ) := by nlinarith
  have hN : (1557182090993/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (5714535078593/31250000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1557182090993/1000000000000:ℝ) (5714535078593/31250000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (145026389/2000000000000:ℝ) ≤ ((1557182090993/1000000000000:ℝ)/(5714535078593/31250000000:ℝ))^2 := by norm_num
  linarith

theorem wc_246 (x : ℝ) (h₁ : (6249/2048:ℝ) ≤ x) (h₂ : x ≤ (25005/8192:ℝ)) : (724782111/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1610679827/10000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (411298599/2500000000:ℝ) := by nlinarith
  have hc1 : (493248586173/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (493248586173/500000000000:ℝ) ≤ taylorCos (411298599/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (246764143393/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1610679827/10000000000:ℝ) + taylorErr ≤ (246764143393/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (160372454953/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (160372454953/1000000000000:ℝ) ≤ taylorSin (1610679827/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (32755656141/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (411298599/2500000000:ℝ) + taylorErr ≤ (32755656141/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-246764143393/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-493248586173/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-32755656141/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-160372454953/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9585845943497/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9589297400271/1000000000000:ℝ) := by nlinarith
  have hp1 : (7932280719003/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (7935136903477/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2599206158421/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-508847732913/200000000000:ℝ) := by nlinarith
  have hN : (1557182090993/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (182909249261689/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1557182090993/1000000000000:ℝ) (182909249261689/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (724782111/10000000000000:ℝ) ≤ ((1557182090993/1000000000000:ℝ)/(182909249261689/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_247 (x : ℝ) (h₁ : (6249/2048:ℝ) ≤ x) (h₂ : x ≤ (1563/512:ℝ)) : (72443249/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1610679827/10000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (1656699251/10000000000:ℝ) := by nlinarith
  have hc1 : (986308094981/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (986308094981/1000000000000:ℝ) ≤ taylorCos (1656699251/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (246764143393/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1610679827/10000000000:ℝ) + taylorErr ≤ (246764143393/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (160372454953/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (160372454953/1000000000000:ℝ) ≤ taylorSin (1610679827/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (4122828069/25000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1656699251/10000000000:ℝ) + taylorErr ≤ (4122828069/25000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-246764143393/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-986308094981/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-4122828069/25000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-160372454953/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9585845943497/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (4795223942931/500000000000:ℝ) := by nlinarith
  have hp1 : (7932280719003/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15872177859001/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-261753041573/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-508847732913/200000000000:ℝ) := by nlinarith
  have hN : (1557182090993/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (18295338130287/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1557182090993/1000000000000:ℝ) (18295338130287/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (72443249/1000000000000:ℝ) ≤ ((1557182090993/1000000000000:ℝ)/(18295338130287/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_248 (x : ℝ) (h₁ : (6249/2048:ℝ) ≤ x) (h₂ : x ≤ (12507/4096:ℝ)) : (723733879/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1610679827/10000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (1679708963/10000000000:ℝ) := by nlinarith
  have hc1 : (246481505997/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (246481505997/250000000000:ℝ) ≤ taylorCos (1679708963/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (246764143393/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1610679827/10000000000:ℝ) + taylorErr ≤ (246764143393/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (160372454953/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (160372454953/1000000000000:ℝ) ≤ taylorSin (1610679827/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (522444221/3125000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1679708963/10000000000:ℝ) + taylorErr ≤ (522444221/3125000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-246764143393/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-246481505997/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-522444221/3125000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-160372454953/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9585845943497/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9592748857043/1000000000000:ℝ) := by nlinarith
  have hp1 : (7932280719003/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3968996490773/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2654181478111/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-508847732913/200000000000:ℝ) := by nlinarith
  have hN : (1557182090993/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (915208306343/5000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1557182090993/1000000000000:ℝ) (915208306343/5000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (723733879/10000000000000:ℝ) ≤ ((1557182090993/1000000000000:ℝ)/(915208306343/5000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_249 (x : ℝ) (h₁ : (6249/2048:ℝ) ≤ x) (h₂ : x ≤ (6255/2048:ℝ)) : (723036111/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1610679827/10000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (68108747/400000000:ℝ) := by nlinarith
  have hc1 : (492769366521/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (492769366521/500000000000:ℝ) ≤ taylorCos (68108747/400000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (246764143393/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1610679827/10000000000:ℝ) + taylorErr ≤ (246764143393/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (160372454953/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (160372454953/1000000000000:ℝ) ≤ taylorSin (1610679827/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (8472514677/50000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (68108747/400000000:ℝ) + taylorErr ≤ (8472514677/50000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-246764143393/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-492769366521/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-8472514677/50000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-160372454953/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9585845943497/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (383801993129/40000000000:ℝ) := by nlinarith
  have hp1 : (7932280719003/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3175958813437/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-67270894151/25000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-508847732913/200000000000:ℝ) := by nlinarith
  have hN : (1557182090993/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (91564981206121/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1557182090993/1000000000000:ℝ) (91564981206121/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (723036111/10000000000000:ℝ) ≤ ((1557182090993/1000000000000:ℝ)/(91564981206121/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_250 (x : ℝ) (h₁ : (6249/2048:ℝ) ≤ x) (h₂ : x ≤ (3129/1024:ℝ)) : (360821549/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1610679827/10000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (1748738099/10000000000:ℝ) := by nlinarith
  have hc1 : (492374249763/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (492374249763/500000000000:ℝ) ≤ taylorCos (1748738099/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (246764143393/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1610679827/10000000000:ℝ) + taylorErr ≤ (246764143393/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (160372454953/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (160372454953/1000000000000:ℝ) ≤ taylorSin (1610679827/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-246764143393/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-492374249763/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-173983875729/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-160372454953/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9585845943497/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9599651770589/1000000000000:ℝ) := by nlinarith
  have hp1 : (7932280719003/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3971852568843/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1382076607503/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-508847732913/200000000000:ℝ) := by nlinarith
  have hN : (1557182090993/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (91653314116573/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1557182090993/1000000000000:ℝ) (91653314116573/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (360821549/5000000000000:ℝ) ≤ ((1557182090993/1000000000000:ℝ)/(91653314116573/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_251 (x : ℝ) (h₁ : (24999/8192:ℝ) ≤ x) (h₂ : x ≤ (25005/8192:ℝ)) : (742112173/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1622184683/10000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (411298599/2500000000:ℝ) := by nlinarith
  have hc1 : (493248586173/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (493248586173/500000000000:ℝ) ≤ taylorCos (411298599/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (123358926771/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1622184683/10000000000:ℝ) + taylorErr ≤ (123358926771/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (80753971469/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (80753971469/500000000000:ℝ) ≤ taylorSin (1622184683/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (32755656141/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (411298599/2500000000:ℝ) + taylorErr ≤ (32755656141/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-123358926771/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-493248586173/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-32755656141/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-80753971469/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (299593638409/31250000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9589297400271/1000000000000:ℝ) := by nlinarith
  have hp1 : (15866465490027/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (7935136903477/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2599206158421/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2562560202991/1000000000000:ℝ) := by nlinarith
  have hN : (1575688788823/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (182909249261689/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1575688788823/1000000000000:ℝ) (182909249261689/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (742112173/10000000000000:ℝ) ≤ ((1575688788823/1000000000000:ℝ)/(182909249261689/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_252 (x : ℝ) (h₁ : (24999/8192:ℝ) ≤ x) (h₂ : x ≤ (1563/512:ℝ)) : (741754191/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1622184683/10000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (1656699251/10000000000:ℝ) := by nlinarith
  have hc1 : (986308094981/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (986308094981/1000000000000:ℝ) ≤ taylorCos (1656699251/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (123358926771/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1622184683/10000000000:ℝ) + taylorErr ≤ (123358926771/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (80753971469/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (80753971469/500000000000:ℝ) ≤ taylorSin (1622184683/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (4122828069/25000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1656699251/10000000000:ℝ) + taylorErr ≤ (4122828069/25000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-123358926771/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-986308094981/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-4122828069/25000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-80753971469/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (299593638409/31250000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (4795223942931/500000000000:ℝ) := by nlinarith
  have hp1 : (15866465490027/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15872177859001/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-261753041573/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2562560202991/1000000000000:ℝ) := by nlinarith
  have hN : (1575688788823/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (18295338130287/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1575688788823/1000000000000:ℝ) (18295338130287/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (741754191/10000000000000:ℝ) ≤ ((1575688788823/1000000000000:ℝ)/(18295338130287/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_253 (x : ℝ) (h₁ : (12501/4096:ℝ) ≤ x) (h₂ : x ≤ (1563/512:ℝ)) : (47455167/625000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1633689539/10000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (1656699251/10000000000:ℝ) := by nlinarith
  have hc1 : (986308094981/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (986308094981/1000000000000:ℝ) ≤ taylorCos (1656699251/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (246671237131/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1633689539/10000000000:ℝ) + taylorErr ≤ (246671237131/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (162643217149/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (162643217149/1000000000000:ℝ) ≤ taylorSin (1633689539/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (4122828069/25000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1656699251/10000000000:ℝ) + taylorErr ≤ (4122828069/25000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-246671237131/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-986308094981/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-4122828069/25000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-162643217149/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9588146914679/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (4795223942931/500000000000:ℝ) := by nlinarith
  have hp1 : (495886548189/31250000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15872177859001/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-261753041573/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2580882673227/1000000000000:ℝ) := by nlinarith
  have hN : (1594197724703/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (18295338130287/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1594197724703/1000000000000:ℝ) (18295338130287/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (47455167/625000000000:ℝ) ≤ ((1594197724703/1000000000000:ℝ)/(18295338130287/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_254 (x : ℝ) (h₁ : (12501/4096:ℝ) ≤ x) (h₂ : x ≤ (25011/8192:ℝ)) : (189729113/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1633689539/10000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (1668204107/10000000000:ℝ) := by nlinarith
  have hc1 : (197223542421/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (197223542421/200000000000:ℝ) ≤ taylorCos (1668204107/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (246671237131/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1633689539/10000000000:ℝ) + taylorErr ≤ (246671237131/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (162643217149/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (162643217149/1000000000000:ℝ) ≤ taylorSin (1633689539/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (20755968329/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1668204107/10000000000:ℝ) + taylorErr ≤ (20755968329/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-246671237131/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-197223542421/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-20755968329/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-162643217149/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9588146914679/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2397899592863/250000000000:ℝ) := by nlinarith
  have hp1 : (495886548189/31250000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (7937040955523/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2635855531181/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2580882673227/1000000000000:ℝ) := by nlinarith
  have hN : (1594197724703/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (91498759319241/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1594197724703/1000000000000:ℝ) (91498759319241/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (189729113/2500000000000:ℝ) ≤ ((1594197724703/1000000000000:ℝ)/(91498759319241/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_255 (x : ℝ) (h₁ : (12501/4096:ℝ) ≤ x) (h₂ : x ≤ (12507/4096:ℝ)) : (758550453/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1633689539/10000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (1679708963/10000000000:ℝ) := by nlinarith
  have hc1 : (246481505997/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (246481505997/250000000000:ℝ) ≤ taylorCos (1679708963/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (246671237131/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1633689539/10000000000:ℝ) + taylorErr ≤ (246671237131/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (162643217149/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (162643217149/1000000000000:ℝ) ≤ taylorSin (1633689539/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (522444221/3125000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1679708963/10000000000:ℝ) + taylorErr ≤ (522444221/3125000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-246671237131/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-246481505997/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-522444221/3125000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-162643217149/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9588146914679/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9592748857043/1000000000000:ℝ) := by nlinarith
  have hp1 : (495886548189/31250000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3968996490773/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2654181478111/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2580882673227/1000000000000:ℝ) := by nlinarith
  have hN : (1594197724703/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (915208306343/5000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1594197724703/1000000000000:ℝ) (915208306343/5000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (758550453/10000000000000:ℝ) ≤ ((1594197724703/1000000000000:ℝ)/(915208306343/5000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_256 (x : ℝ) (h₁ : (12501/4096:ℝ) ≤ x) (h₂ : x ≤ (6255/2048:ℝ)) : (378909559/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1633689539/10000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (68108747/400000000:ℝ) := by nlinarith
  have hc1 : (492769366521/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (492769366521/500000000000:ℝ) ≤ taylorCos (68108747/400000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (246671237131/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1633689539/10000000000:ℝ) + taylorErr ≤ (246671237131/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (162643217149/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (162643217149/1000000000000:ℝ) ≤ taylorSin (1633689539/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (8472514677/50000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (68108747/400000000:ℝ) + taylorErr ≤ (8472514677/50000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-246671237131/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-492769366521/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-8472514677/50000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-162643217149/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9588146914679/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (383801993129/40000000000:ℝ) := by nlinarith
  have hp1 : (495886548189/31250000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3175958813437/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-67270894151/25000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2580882673227/1000000000000:ℝ) := by nlinarith
  have hN : (1594197724703/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (91564981206121/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1594197724703/1000000000000:ℝ) (91564981206121/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (378909559/5000000000000:ℝ) ≤ ((1594197724703/1000000000000:ℝ)/(91564981206121/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_257 (x : ℝ) (h₁ : (25005/8192:ℝ) ≤ x) (h₂ : x ≤ (25011/8192:ℝ)) : (97080401/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (329038879/2000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (1668204107/10000000000:ℝ) := by nlinarith
  have hc1 : (197223542421/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (197223542421/200000000000:ℝ) ≤ taylorCos (1668204107/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (986497176887/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (329038879/2000000000:ℝ) + taylorErr ≤ (986497176887/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (81889138041/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (81889138041/500000000000:ℝ) ≤ taylorSin (329038879/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (20755968329/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1668204107/10000000000:ℝ) + taylorErr ≤ (20755968329/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-986497176887/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-197223542421/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-20755968329/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-81889138041/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (958929740027/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2397899592863/250000000000:ℝ) := by nlinarith
  have hp1 : (15870273594069/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (7937040955523/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2635855531181/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1299603025093/500000000000:ℝ) := by nlinarith
  have hN : (1612708873299/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (91498759319241/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1612708873299/1000000000000:ℝ) (91498759319241/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (97080401/1250000000000:ℝ) ≤ ((1612708873299/1000000000000:ℝ)/(91498759319241/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_258 (x : ℝ) (h₁ : (25005/8192:ℝ) ≤ x) (h₂ : x ≤ (12507/4096:ℝ)) : (776268661/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (329038879/2000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (1679708963/10000000000:ℝ) := by nlinarith
  have hc1 : (246481505997/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (246481505997/250000000000:ℝ) ≤ taylorCos (1679708963/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (986497176887/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (329038879/2000000000:ℝ) + taylorErr ≤ (986497176887/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (81889138041/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (81889138041/500000000000:ℝ) ≤ taylorSin (329038879/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (522444221/3125000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1679708963/10000000000:ℝ) + taylorErr ≤ (522444221/3125000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-986497176887/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-246481505997/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-522444221/3125000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-81889138041/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (958929740027/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9592748857043/1000000000000:ℝ) := by nlinarith
  have hp1 : (15870273594069/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3968996490773/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2654181478111/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1299603025093/500000000000:ℝ) := by nlinarith
  have hN : (1612708873299/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (915208306343/5000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1612708873299/1000000000000:ℝ) (915208306343/5000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (776268661/10000000000000:ℝ) ≤ ((1612708873299/1000000000000:ℝ)/(915208306343/5000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_259 (x : ℝ) (h₁ : (1563/512:ℝ) ≤ x) (h₂ : x ≤ (12507/4096:ℝ)) : (158838709/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (6626797/40000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (1679708963/10000000000:ℝ) := by nlinarith
  have hc1 : (246481505997/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (246481505997/250000000000:ℝ) ≤ taylorCos (1679708963/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (493154049761/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (6626797/40000000:ℝ) + taylorErr ≤ (493154049761/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (164913118137/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (164913118137/1000000000000:ℝ) ≤ taylorSin (6626797/40000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (522444221/3125000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1679708963/10000000000:ℝ) + taylorErr ≤ (522444221/3125000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-493154049761/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-246481505997/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-522444221/3125000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-164913118137/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9590447885861/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9592748857043/1000000000000:ℝ) := by nlinarith
  have hp1 : (1587217764609/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3968996490773/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2654181478111/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2617530307241/1000000000000:ℝ) := by nlinarith
  have hN : (1631222207719/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (915208306343/5000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1631222207719/1000000000000:ℝ) (915208306343/5000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (158838709/2000000000000:ℝ) ≤ ((1631222207719/1000000000000:ℝ)/(915208306343/5000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_260 (x : ℝ) (h₁ : (1563/512:ℝ) ≤ x) (h₂ : x ≤ (25017/8192:ℝ)) : (39690529/500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (6626797/40000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (1691213819/10000000000:ℝ) := by nlinarith
  have hc1 : (492866515441/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (492866515441/500000000000:ℝ) ≤ taylorCos (1691213819/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (493154049761/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (6626797/40000000:ℝ) + taylorErr ≤ (493154049761/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (164913118137/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (164913118137/1000000000000:ℝ) ≤ taylorSin (6626797/40000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (168316333523/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1691213819/10000000000:ℝ) + taylorErr ≤ (168316333523/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-493154049761/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-492866515441/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-168316333523/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-164913118137/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9590447885861/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (4796949671317/500000000000:ℝ) := by nlinarith
  have hp1 : (1587217764609/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15877890015139/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-267250823143/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2617530307241/1000000000000:ℝ) := by nlinarith
  have hN : (1631222207719/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (183085809193187/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1631222207719/1000000000000:ℝ) (183085809193187/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (39690529/500000000000:ℝ) ≤ ((1631222207719/1000000000000:ℝ)/(183085809193187/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_261 (x : ℝ) (h₁ : (1563/512:ℝ) ≤ x) (h₂ : x ≤ (6255/2048:ℝ)) : (158685569/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (6626797/40000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (68108747/400000000:ℝ) := by nlinarith
  have hc1 : (492769366521/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (492769366521/500000000000:ℝ) ≤ taylorCos (68108747/400000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (493154049761/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (6626797/40000000:ℝ) + taylorErr ≤ (493154049761/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (164913118137/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (164913118137/1000000000000:ℝ) ≤ taylorSin (6626797/40000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (8472514677/50000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (68108747/400000000:ℝ) + taylorErr ≤ (8472514677/50000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-493154049761/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-492769366521/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-8472514677/50000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-164913118137/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9590447885861/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (383801993129/40000000000:ℝ) := by nlinarith
  have hp1 : (1587217764609/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3175958813437/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-67270894151/25000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2617530307241/1000000000000:ℝ) := by nlinarith
  have hN : (1631222207719/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (91564981206121/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1631222207719/1000000000000:ℝ) (91564981206121/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (158685569/2000000000000:ℝ) ≤ ((1631222207719/1000000000000:ℝ)/(91564981206121/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_262 (x : ℝ) (h₁ : (1563/512:ℝ) ≤ x) (h₂ : x ≤ (12513/4096:ℝ)) : (792663069/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (6626797/40000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (1725728387/10000000000:ℝ) := by nlinarith
  have hc1 : (246286556049/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (246286556049/250000000000:ℝ) ≤ taylorCos (1725728387/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (493154049761/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (6626797/40000000:ℝ) + taylorErr ≤ (493154049761/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (164913118137/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (164913118137/1000000000000:ℝ) ≤ taylorSin (6626797/40000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (171717539211/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1725728387/10000000000:ℝ) + taylorErr ≤ (171717539211/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-493154049761/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-246286556049/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-171717539211/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-164913118137/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9590447885861/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9597350799407/1000000000000:ℝ) := by nlinarith
  have hp1 : (1587217764609/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (7941801085639/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2727493078659/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2617530307241/1000000000000:ℝ) := by nlinarith
  have hN : (1631222207719/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (183218284733757/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1631222207719/1000000000000:ℝ) (183218284733757/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (792663069/10000000000000:ℝ) ≤ ((1631222207719/1000000000000:ℝ)/(183218284733757/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_263 (x : ℝ) (h₁ : (1563/512:ℝ) ≤ x) (h₂ : x ≤ (3129/1024:ℝ)) : (158379843/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (6626797/40000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (1748738099/10000000000:ℝ) := by nlinarith
  have hc1 : (492374249763/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (492374249763/500000000000:ℝ) ≤ taylorCos (1748738099/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (493154049761/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (6626797/40000000:ℝ) + taylorErr ≤ (493154049761/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (164913118137/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (164913118137/1000000000000:ℝ) ≤ taylorSin (6626797/40000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-493154049761/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-492374249763/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-173983875729/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-164913118137/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9590447885861/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9599651770589/1000000000000:ℝ) := by nlinarith
  have hp1 : (1587217764609/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3971852568843/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1382076607503/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2617530307241/1000000000000:ℝ) := by nlinarith
  have hN : (1631222207719/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (91653314116573/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1631222207719/1000000000000:ℝ) (91653314116573/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (158379843/2000000000000:ℝ) ≤ ((1631222207719/1000000000000:ℝ)/(91653314116573/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_264 (x : ℝ) (h₁ : (1563/512:ℝ) ≤ x) (h₂ : x ≤ (6261/2048:ℝ)) : (197593567/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (6626797/40000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (897378761/5000000000:ℝ) := by nlinarith
  have hc1 : (61496088199/62500000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (61496088199/62500000000:ℝ) ≤ taylorCos (897378761/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (493154049761/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (6626797/40000000:ℝ) + taylorErr ≤ (493154049761/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (164913118137/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (164913118137/1000000000000:ℝ) ≤ taylorSin (6626797/40000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (89256886609/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (897378761/5000000000:ℝ) + taylorErr ≤ (89256886609/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-493154049761/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-61496088199/62500000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-89256886609/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-164913118137/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9590447885861/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1200531714119/125000000000:ℝ) := by nlinarith
  have hp1 : (1587217764609/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3973756620889/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-141874057649/50000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2617530307241/1000000000000:ℝ) := by nlinarith
  have hN : (1631222207719/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (36696675753101/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1631222207719/1000000000000:ℝ) (36696675753101/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (197593567/2500000000000:ℝ) ≤ ((1631222207719/1000000000000:ℝ)/(36696675753101/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_265 (x : ℝ) (h₁ : (1563/512:ℝ) ≤ x) (h₂ : x ≤ (783/256:ℝ)) : (394426497/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (6626797/40000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (920388473/5000000000:ℝ) := by nlinarith
  have hc1 : (983105485159/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (983105485159/1000000000000:ℝ) ≤ taylorCos (920388473/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (493154049761/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (6626797/40000000:ℝ) + taylorErr ≤ (493154049761/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (164913118137/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (164913118137/1000000000000:ℝ) ≤ taylorSin (6626797/40000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (18303989027/100000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (920388473/5000000000:ℝ) + taylorErr ≤ (18303989027/100000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-493154049761/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-983105485159/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-18303989027/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-164913118137/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9590447885861/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2402213913829/250000000000:ℝ) := by nlinarith
  have hp1 : (1587217764609/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (7951321345871/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-29108179733/10000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2617530307241/1000000000000:ℝ) := by nlinarith
  have hN : (1631222207719/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (183660214009397/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1631222207719/1000000000000:ℝ) (183660214009397/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (394426497/5000000000000:ℝ) ≤ ((1631222207719/1000000000000:ℝ)/(183660214009397/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_266 (x : ℝ) (h₁ : (1563/512:ℝ) ≤ x) (h₂ : x ≤ (3135/1024:ℝ)) : (785821423/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (6626797/40000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (1932815793/10000000000:ℝ) := by nlinarith
  have hc1 : (981379191047/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (981379191047/1000000000000:ℝ) ≤ taylorCos (1932815793/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (493154049761/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (6626797/40000000:ℝ) + taylorErr ≤ (493154049761/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (164913118137/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (164913118137/1000000000000:ℝ) ≤ taylorSin (6626797/40000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (96040199669/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1932815793/10000000000:ℝ) + taylorErr ≤ (96040199669/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-493154049761/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-981379191047/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-96040199669/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-164913118137/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9590447885861/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9618059540043/1000000000000:ℝ) := by nlinarith
  have hp1 : (1587217764609/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15917875108113/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-3057511807379/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2617530307241/1000000000000:ℝ) := by nlinarith
  have hN : (1631222207719/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (1472113109053/8000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1631222207719/1000000000000:ℝ) (1472113109053/8000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (785821423/10000000000000:ℝ) ≤ ((1631222207719/1000000000000:ℝ)/(1472113109053/8000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_267 (x : ℝ) (h₁ : (25011/8192:ℝ) ≤ x) (h₂ : x ≤ (25017/8192:ℝ)) : (811933449/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (834102053/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (1691213819/10000000000:ℝ) := by nlinarith
  have hc1 : (492866515441/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (492866515441/500000000000:ℝ) ≤ taylorCos (1691213819/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (493058858323/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (834102053/5000000000:ℝ) + taylorErr ≤ (493058858323/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (166047742009/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (166047742009/1000000000000:ℝ) ≤ taylorSin (834102053/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (168316333523/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1691213819/10000000000:ℝ) + taylorErr ≤ (168316333523/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-493058858323/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-492866515441/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-168316333523/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-166047742009/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9591598371451/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (4796949671317/500000000000:ℝ) := by nlinarith
  have hp1 : (15874081698109/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15877890015139/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-267250823143/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2635855422437/1000000000000:ℝ) := by nlinarith
  have hN : (1649737705791/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (183085809193187/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1649737705791/1000000000000:ℝ) (183085809193187/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (811933449/10000000000000:ℝ) ≤ ((1649737705791/1000000000000:ℝ)/(183085809193187/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_268 (x : ℝ) (h₁ : (25011/8192:ℝ) ≤ x) (h₂ : x ≤ (6255/2048:ℝ)) : (811541977/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (834102053/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (68108747/400000000:ℝ) := by nlinarith
  have hc1 : (492769366521/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (492769366521/500000000000:ℝ) ≤ taylorCos (68108747/400000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (493058858323/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (834102053/5000000000:ℝ) + taylorErr ≤ (493058858323/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (166047742009/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (166047742009/1000000000000:ℝ) ≤ taylorSin (834102053/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (8472514677/50000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (68108747/400000000:ℝ) + taylorErr ≤ (8472514677/50000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-493058858323/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-492769366521/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-8472514677/50000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-166047742009/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9591598371451/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (383801993129/40000000000:ℝ) := by nlinarith
  have hp1 : (15874081698109/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3175958813437/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-67270894151/25000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2635855422437/1000000000000:ℝ) := by nlinarith
  have hN : (1649737705791/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (91564981206121/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1649737705791/1000000000000:ℝ) (91564981206121/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (811541977/10000000000000:ℝ) ≤ ((1649737705791/1000000000000:ℝ)/(91564981206121/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_269 (x : ℝ) (h₁ : (12507/4096:ℝ) ≤ x) (h₂ : x ≤ (6255/2048:ℝ)) : (829862681/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (839854481/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (68108747/400000000:ℝ) := by nlinarith
  have hc1 : (492769366521/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (492769366521/500000000000:ℝ) ≤ taylorCos (68108747/400000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (985926028529/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (839854481/5000000000:ℝ) + taylorErr ≤ (985926028529/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (167182146097/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (167182146097/1000000000000:ℝ) ≤ taylorSin (839854481/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (8472514677/50000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (68108747/400000000:ℝ) + taylorErr ≤ (8472514677/50000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-985926028529/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-492769366521/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-8472514677/50000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-167182146097/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (4796374428521/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (383801993129/40000000000:ℝ) := by nlinarith
  have hp1 : (1587598575013/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3175958813437/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-67270894151/25000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-331772671139/125000000000:ℝ) := by nlinarith
  have hN : (1668255340583/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (91564981206121/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1668255340583/1000000000000:ℝ) (91564981206121/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (829862681/10000000000000:ℝ) ≤ ((1668255340583/1000000000000:ℝ)/(91564981206121/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_270 (x : ℝ) (h₁ : (12507/4096:ℝ) ≤ x) (h₂ : x ≤ (25023/8192:ℝ)) : (829462613/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (839854481/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (1714223531/10000000000:ℝ) := by nlinarith
  have hc1 : (123167891341/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (123167891341/125000000000:ℝ) ≤ taylorCos (1714223531/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (985926028529/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (839854481/5000000000:ℝ) + taylorErr ≤ (985926028529/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (167182146097/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (167182146097/1000000000000:ℝ) ≤ taylorSin (839854481/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (17058402927/100000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1714223531/10000000000:ℝ) + taylorErr ≤ (17058402927/100000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-985926028529/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-123167891341/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-17058402927/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-167182146097/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (4796374428521/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1199525039227/125000000000:ℝ) := by nlinarith
  have hp1 : (1587598575013/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (248151533113/15625000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2709164056829/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-331772671139/125000000000:ℝ) := by nlinarith
  have hN : (1668255340583/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (36634824185153/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1668255340583/1000000000000:ℝ) (36634824185153/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (829462613/10000000000000:ℝ) ≤ ((1668255340583/1000000000000:ℝ)/(36634824185153/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_271 (x : ℝ) (h₁ : (12507/4096:ℝ) ≤ x) (h₂ : x ≤ (12513/4096:ℝ)) : (414531393/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (839854481/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (1725728387/10000000000:ℝ) := by nlinarith
  have hc1 : (246286556049/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (246286556049/250000000000:ℝ) ≤ taylorCos (1725728387/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (985926028529/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (839854481/5000000000:ℝ) + taylorErr ≤ (985926028529/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (167182146097/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (167182146097/1000000000000:ℝ) ≤ taylorSin (839854481/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (171717539211/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1725728387/10000000000:ℝ) + taylorErr ≤ (171717539211/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-985926028529/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-246286556049/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-171717539211/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-167182146097/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (4796374428521/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9597350799407/1000000000000:ℝ) := by nlinarith
  have hp1 : (1587598575013/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (7941801085639/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2727493078659/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-331772671139/125000000000:ℝ) := by nlinarith
  have hN : (1668255340583/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (183218284733757/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1668255340583/1000000000000:ℝ) (183218284733757/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (414531393/5000000000000:ℝ) ≤ ((1668255340583/1000000000000:ℝ)/(183218284733757/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_272 (x : ℝ) (h₁ : (12507/4096:ℝ) ≤ x) (h₂ : x ≤ (3129/1024:ℝ)) : (165652771/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (839854481/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (1748738099/10000000000:ℝ) := by nlinarith
  have hc1 : (492374249763/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (492374249763/500000000000:ℝ) ≤ taylorCos (1748738099/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (985926028529/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (839854481/5000000000:ℝ) + taylorErr ≤ (985926028529/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (167182146097/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (167182146097/1000000000000:ℝ) ≤ taylorSin (839854481/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-985926028529/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-492374249763/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-173983875729/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-167182146097/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (4796374428521/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9599651770589/1000000000000:ℝ) := by nlinarith
  have hp1 : (1587598575013/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3971852568843/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1382076607503/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-331772671139/125000000000:ℝ) := by nlinarith
  have hN : (1668255340583/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (91653314116573/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1668255340583/1000000000000:ℝ) (91653314116573/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (165652771/2000000000000:ℝ) ≤ ((1668255340583/1000000000000:ℝ)/(91653314116573/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_273 (x : ℝ) (h₁ : (25017/8192:ℝ) ≤ x) (h₂ : x ≤ (25023/8192:ℝ)) : (211995251/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (845606909/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (1714223531/10000000000:ℝ) := by nlinarith
  have hc1 : (123167891341/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (123167891341/125000000000:ℝ) ≤ taylorCos (1714223531/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (985733035423/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (845606909/5000000000:ℝ) + taylorErr ≤ (985733035423/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (168316328901/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (168316328901/1000000000000:ℝ) ≤ taylorSin (845606909/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (17058402927/100000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1714223531/10000000000:ℝ) + taylorErr ≤ (17058402927/100000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-985733035423/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-123167891341/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-17058402927/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-168316328901/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9593899342633/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1199525039227/125000000000:ℝ) := by nlinarith
  have hp1 : (1984736225269/125000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (248151533113/15625000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2709164056829/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-167031757637/62500000000:ℝ) := by nlinarith
  have hN : (1686775086769/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (36634824185153/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1686775086769/1000000000000:ℝ) (36634824185153/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (211995251/2500000000000:ℝ) ≤ ((1686775086769/1000000000000:ℝ)/(36634824185153/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_274 (x : ℝ) (h₁ : (25017/8192:ℝ) ≤ x) (h₂ : x ≤ (12513/4096:ℝ)) : (847572251/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (845606909/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (1725728387/10000000000:ℝ) := by nlinarith
  have hc1 : (246286556049/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (246286556049/250000000000:ℝ) ≤ taylorCos (1725728387/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (985733035423/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (845606909/5000000000:ℝ) + taylorErr ≤ (985733035423/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (168316328901/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (168316328901/1000000000000:ℝ) ≤ taylorSin (845606909/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (171717539211/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1725728387/10000000000:ℝ) + taylorErr ≤ (171717539211/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-985733035423/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-246286556049/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-171717539211/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-168316328901/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9593899342633/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9597350799407/1000000000000:ℝ) := by nlinarith
  have hp1 : (1984736225269/125000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (7941801085639/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2727493078659/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-167031757637/62500000000:ℝ) := by nlinarith
  have hN : (1686775086769/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (183218284733757/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1686775086769/1000000000000:ℝ) (183218284733757/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (847572251/10000000000000:ℝ) ≤ ((1686775086769/1000000000000:ℝ)/(183218284733757/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_275 (x : ℝ) (h₁ : (6255/2048:ℝ) ≤ x) (h₂ : x ≤ (12513/4096:ℝ)) : (43314409/500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (851359337/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (1725728387/10000000000:ℝ) := by nlinarith
  have hc1 : (246286556049/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (246286556049/250000000000:ℝ) ≤ taylorCos (1725728387/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (61596171099/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (851359337/5000000000:ℝ) + taylorErr ≤ (61596171099/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (169450288917/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (169450288917/1000000000000:ℝ) ≤ taylorSin (851359337/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (171717539211/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1725728387/10000000000:ℝ) + taylorErr ≤ (171717539211/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-61596171099/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-246286556049/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-171717539211/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-169450288917/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (74961326783/7812500000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9597350799407/1000000000000:ℝ) := by nlinarith
  have hp1 : (15879793854173/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (7941801085639/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2727493078659/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-672708914133/250000000000:ℝ) := by nlinarith
  have hN : (426324229737/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (183218284733757/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (426324229737/250000000000:ℝ) (183218284733757/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (43314409/500000000000:ℝ) ≤ ((426324229737/250000000000:ℝ)/(183218284733757/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_276 (x : ℝ) (h₁ : (6255/2048:ℝ) ≤ x) (h₂ : x ≤ (25029/8192:ℝ)) : (216467663/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (851359337/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (1737233243/10000000000:ℝ) := by nlinarith
  have hc1 : (246237003427/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (246237003427/250000000000:ℝ) ≤ taylorCos (1737233243/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (61596171099/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (851359337/5000000000:ℝ) + taylorErr ≤ (61596171099/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (169450288917/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (169450288917/1000000000000:ℝ) ≤ taylorSin (851359337/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (21606352733/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1737233243/10000000000:ℝ) + taylorErr ≤ (21606352733/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-61596171099/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-246237003427/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-21606352733/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-169450288917/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (74961326783/7812500000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (4799250642499/500000000000:ℝ) := by nlinarith
  have hp1 : (15879793854173/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (635420248933/40000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-686455701607/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-672708914133/250000000000:ℝ) := by nlinarith
  have hN : (426324229737/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (183262453836217/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (426324229737/250000000000:ℝ) (183262453836217/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (216467663/2500000000000:ℝ) ≤ ((426324229737/250000000000:ℝ)/(183262453836217/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_277 (x : ℝ) (h₁ : (6255/2048:ℝ) ≤ x) (h₂ : x ≤ (3129/1024:ℝ)) : (13522709/156250000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (851359337/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (1748738099/10000000000:ℝ) := by nlinarith
  have hc1 : (492374249763/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (492374249763/500000000000:ℝ) ≤ taylorCos (1748738099/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (61596171099/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (851359337/5000000000:ℝ) + taylorErr ≤ (61596171099/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (169450288917/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (169450288917/1000000000000:ℝ) ≤ taylorSin (851359337/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-61596171099/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-492374249763/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-173983875729/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-169450288917/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (74961326783/7812500000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9599651770589/1000000000000:ℝ) := by nlinarith
  have hp1 : (15879793854173/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3971852568843/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1382076607503/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-672708914133/250000000000:ℝ) := by nlinarith
  have hN : (426324229737/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (91653314116573/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (426324229737/250000000000:ℝ) (91653314116573/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (13522709/156250000000:ℝ) ≤ ((426324229737/250000000000:ℝ)/(91653314116573/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_278 (x : ℝ) (h₁ : (6255/2048:ℝ) ≤ x) (h₂ : x ≤ (12519/4096:ℝ)) : (864619579/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (851359337/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (1771747811/10000000000:ℝ) := by nlinarith
  have hc1 : (492172780569/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (492172780569/500000000000:ℝ) ≤ taylorCos (1771747811/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (61596171099/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (851359337/5000000000:ℝ) + taylorErr ≤ (61596171099/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (169450288917/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (169450288917/1000000000000:ℝ) ≤ taylorSin (851359337/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (22031161387/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1771747811/10000000000:ℝ) + taylorErr ≤ (22031161387/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-61596171099/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-492172780569/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-22031161387/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-169450288917/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (74961326783/7812500000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9601952741771/1000000000000:ℝ) := by nlinarith
  have hp1 : (15879793854173/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3178243675893/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2800815974033/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-672708914133/250000000000:ℝ) := by nlinarith
  have hN : (426324229737/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (22924374113801/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (426324229737/250000000000:ℝ) (22924374113801/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (864619579/10000000000000:ℝ) ≤ ((426324229737/250000000000:ℝ)/(22924374113801/125000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_279 (x : ℝ) (h₁ : (6255/2048:ℝ) ≤ x) (h₂ : x ≤ (6261/2048:ℝ)) : (215946697/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (851359337/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (897378761/5000000000:ℝ) := by nlinarith
  have hc1 : (61496088199/62500000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (61496088199/62500000000:ℝ) ≤ taylorCos (897378761/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (61596171099/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (851359337/5000000000:ℝ) + taylorErr ≤ (61596171099/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (169450288917/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (169450288917/1000000000000:ℝ) ≤ taylorSin (851359337/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (89256886609/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (897378761/5000000000:ℝ) + taylorErr ≤ (89256886609/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-61596171099/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-61496088199/62500000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-89256886609/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-169450288917/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (74961326783/7812500000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1200531714119/125000000000:ℝ) := by nlinarith
  have hp1 : (15879793854173/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3973756620889/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-141874057649/50000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-672708914133/250000000000:ℝ) := by nlinarith
  have hN : (426324229737/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (36696675753101/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (426324229737/250000000000:ℝ) (36696675753101/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (215946697/2500000000000:ℝ) ≤ ((426324229737/250000000000:ℝ)/(36696675753101/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_280 (x : ℝ) (h₁ : (6255/2048:ℝ) ≤ x) (h₂ : x ≤ (783/256:ℝ)) : (862124213/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (851359337/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (920388473/5000000000:ℝ) := by nlinarith
  have hc1 : (983105485159/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (983105485159/1000000000000:ℝ) ≤ taylorCos (920388473/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (61596171099/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (851359337/5000000000:ℝ) + taylorErr ≤ (61596171099/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (169450288917/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (169450288917/1000000000000:ℝ) ≤ taylorSin (851359337/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (18303989027/100000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (920388473/5000000000:ℝ) + taylorErr ≤ (18303989027/100000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-61596171099/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-983105485159/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-18303989027/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-169450288917/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (74961326783/7812500000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2402213913829/250000000000:ℝ) := by nlinarith
  have hp1 : (15879793854173/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (7951321345871/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-29108179733/10000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-672708914133/250000000000:ℝ) := by nlinarith
  have hN : (426324229737/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (183660214009397/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (426324229737/250000000000:ℝ) (183660214009397/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (862124213/10000000000000:ℝ) ≤ ((426324229737/250000000000:ℝ)/(183660214009397/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_281 (x : ℝ) (h₁ : (25023/8192:ℝ) ≤ x) (h₂ : x ≤ (25029/8192:ℝ)) : (884783967/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (171422353/1000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (1737233243/10000000000:ℝ) := by nlinarith
  have hc1 : (246237003427/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (246237003427/250000000000:ℝ) ≤ taylorCos (1737233243/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (985343135269/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (171422353/1000000000:ℝ) + taylorErr ≤ (985343135269/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (170584024647/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (170584024647/1000000000000:ℝ) ≤ taylorSin (171422353/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (21606352733/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1737233243/10000000000:ℝ) + taylorErr ≤ (21606352733/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-985343135269/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-246237003427/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-21606352733/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-170584024647/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1919240062763/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (4799250642499/500000000000:ℝ) := by nlinarith
  have hp1 : (7940848953097/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (635420248933/40000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-686455701607/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1354581973533/500000000000:ℝ) := by nlinarith
  have hN : (1723820811797/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (183262453836217/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1723820811797/1000000000000:ℝ) (183262453836217/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (884783967/10000000000000:ℝ) ≤ ((1723820811797/1000000000000:ℝ)/(183262453836217/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_282 (x : ℝ) (h₁ : (25023/8192:ℝ) ≤ x) (h₂ : x ≤ (3129/1024:ℝ)) : (884357577/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (171422353/1000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (1748738099/10000000000:ℝ) := by nlinarith
  have hc1 : (492374249763/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (492374249763/500000000000:ℝ) ≤ taylorCos (1748738099/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (985343135269/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (171422353/1000000000:ℝ) + taylorErr ≤ (985343135269/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (170584024647/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (170584024647/1000000000000:ℝ) ≤ taylorSin (171422353/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-985343135269/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-492374249763/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-173983875729/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-170584024647/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1919240062763/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9599651770589/1000000000000:ℝ) := by nlinarith
  have hp1 : (7940848953097/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3971852568843/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1382076607503/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1354581973533/500000000000:ℝ) := by nlinarith
  have hN : (1723820811797/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (91653314116573/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1723820811797/1000000000000:ℝ) (91653314116573/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (884357577/10000000000000:ℝ) ≤ ((1723820811797/1000000000000:ℝ)/(91653314116573/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_283 (x : ℝ) (h₁ : (12513/4096:ℝ) ≤ x) (h₂ : x ≤ (3129/1024:ℝ)) : (903468127/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (862864193/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (1748738099/10000000000:ℝ) := by nlinarith
  have hc1 : (492374249763/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (492374249763/500000000000:ℝ) ≤ taylorCos (1748738099/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (985146228737/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (862864193/5000000000:ℝ) + taylorErr ≤ (985146228737/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (42929383647/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (42929383647/250000000000:ℝ) ≤ taylorSin (862864193/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-985146228737/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-492374249763/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-173983875729/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-42929383647/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (4798675399703/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9599651770589/1000000000000:ℝ) := by nlinarith
  have hp1 : (3176720391643/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3971852568843/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1382076607503/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2727492968641/1000000000000:ℝ) := by nlinarith
  have hN : (27224167811/15625000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (91653314116573/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (27224167811/15625000000:ℝ) (91653314116573/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (903468127/10000000000000:ℝ) ≤ ((27224167811/15625000000:ℝ)/(91653314116573/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_284 (x : ℝ) (h₁ : (12513/4096:ℝ) ≤ x) (h₂ : x ≤ (25035/8192:ℝ)) : (180606557/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (862864193/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (352048591/2000000000:ℝ) := by nlinarith
  have hc1 : (492273840957/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (492273840957/500000000000:ℝ) ≤ taylorCos (352048591/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (985146228737/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (862864193/5000000000:ℝ) + taylorErr ≤ (985146228737/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (42929383647/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (42929383647/250000000000:ℝ) ≤ taylorSin (862864193/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (87558349653/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (352048591/2000000000:ℝ) + taylorErr ≤ (87558349653/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-985146228737/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-492273840957/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-87558349653/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-42929383647/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (4798675399703/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (480040112809/50000000000:ℝ) := by nlinarith
  have hp1 : (3176720391643/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (7944657163709/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2782484279253/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2727492968641/1000000000000:ℝ) := by nlinarith
  have hN : (27224167811/15625000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (91675403962271/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (27224167811/15625000000:ℝ) (91675403962271/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (180606557/2000000000000:ℝ) ≤ ((27224167811/15625000000:ℝ)/(91675403962271/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_285 (x : ℝ) (h₁ : (12513/4096:ℝ) ≤ x) (h₂ : x ≤ (12519/4096:ℝ)) : (451298853/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (862864193/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (1771747811/10000000000:ℝ) := by nlinarith
  have hc1 : (492172780569/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (492172780569/500000000000:ℝ) ≤ taylorCos (1771747811/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (985146228737/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (862864193/5000000000:ℝ) + taylorErr ≤ (985146228737/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (42929383647/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (42929383647/250000000000:ℝ) ≤ taylorSin (862864193/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (22031161387/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1771747811/10000000000:ℝ) + taylorErr ≤ (22031161387/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-985146228737/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-492172780569/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-22031161387/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-42929383647/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (4798675399703/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9601952741771/1000000000000:ℝ) := by nlinarith
  have hp1 : (3176720391643/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3178243675893/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2800815974033/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2727492968641/1000000000000:ℝ) := by nlinarith
  have hN : (27224167811/15625000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (22924374113801/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (27224167811/15625000000:ℝ) (22924374113801/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (451298853/5000000000000:ℝ) ≤ ((27224167811/15625000000:ℝ)/(22924374113801/125000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_286 (x : ℝ) (h₁ : (12513/4096:ℝ) ≤ x) (h₂ : x ≤ (6261/2048:ℝ)) : (450864167/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (862864193/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (897378761/5000000000:ℝ) := by nlinarith
  have hc1 : (61496088199/62500000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (61496088199/62500000000:ℝ) ≤ taylorCos (897378761/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (985146228737/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (862864193/5000000000:ℝ) + taylorErr ≤ (985146228737/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (42929383647/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (42929383647/250000000000:ℝ) ≤ taylorSin (862864193/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (89256886609/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (897378761/5000000000:ℝ) + taylorErr ≤ (89256886609/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-985146228737/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-61496088199/62500000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-89256886609/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-42929383647/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (4798675399703/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1200531714119/125000000000:ℝ) := by nlinarith
  have hp1 : (3176720391643/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3973756620889/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-141874057649/50000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2727492968641/1000000000000:ℝ) := by nlinarith
  have hN : (27224167811/15625000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (36696675753101/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (27224167811/15625000000:ℝ) (36696675753101/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (450864167/5000000000000:ℝ) ≤ ((27224167811/15625000000:ℝ)/(36696675753101/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_287 (x : ℝ) (h₁ : (25029/8192:ℝ) ≤ x) (h₂ : x ≤ (25035/8192:ℝ)) : (461170209/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (868616621/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (352048591/2000000000:ℝ) := by nlinarith
  have hc1 : (492273840957/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (492273840957/500000000000:ℝ) ≤ taylorCos (352048591/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (984948018249/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (868616621/5000000000:ℝ) + taylorErr ≤ (984948018249/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (86425408621/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (86425408621/500000000000:ℝ) ≤ taylorSin (868616621/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (87558349653/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (352048591/2000000000:ℝ) + taylorErr ≤ (87558349653/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-984948018249/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-492273840957/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-87558349653/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-86425408621/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9598501284997/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (480040112809/50000000000:ℝ) := by nlinarith
  have hp1 : (3971376502559/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (7944657163709/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2782484279253/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2745822696171/1000000000000:ℝ) := by nlinarith
  have hN : (880437338961/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (91675403962271/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (880437338961/500000000000:ℝ) (91675403962271/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (461170209/5000000000000:ℝ) ≤ ((880437338961/500000000000:ℝ)/(91675403962271/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_288 (x : ℝ) (h₁ : (25029/8192:ℝ) ≤ x) (h₂ : x ≤ (12519/4096:ℝ)) : (230474009/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (868616621/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (1771747811/10000000000:ℝ) := by nlinarith
  have hc1 : (492172780569/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (492172780569/500000000000:ℝ) ≤ taylorCos (1771747811/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (984948018249/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (868616621/5000000000:ℝ) + taylorErr ≤ (984948018249/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (86425408621/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (86425408621/500000000000:ℝ) ≤ taylorSin (868616621/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (22031161387/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1771747811/10000000000:ℝ) + taylorErr ≤ (22031161387/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-984948018249/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-492172780569/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-22031161387/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-86425408621/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9598501284997/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9601952741771/1000000000000:ℝ) := by nlinarith
  have hp1 : (3971376502559/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3178243675893/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2800815974033/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2745822696171/1000000000000:ℝ) := by nlinarith
  have hN : (880437338961/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (22924374113801/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (880437338961/500000000000:ℝ) (22924374113801/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (230474009/2500000000000:ℝ) ≤ ((880437338961/500000000000:ℝ)/(22924374113801/125000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_289 (x : ℝ) (h₁ : (3129/1024:ℝ) ≤ x) (h₂ : x ≤ (12519/4096:ℝ)) : (941400597/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (874369049/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (1771747811/10000000000:ℝ) := by nlinarith
  have hc1 : (492172780569/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (492172780569/500000000000:ℝ) ≤ taylorCos (1771747811/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (984748504067/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (874369049/5000000000:ℝ) + taylorErr ≤ (984748504067/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (173983871107/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (173983871107/1000000000000:ℝ) ≤ taylorSin (874369049/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (22031161387/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1771747811/10000000000:ℝ) + taylorErr ≤ (22031161387/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (-492172780569/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-22031161387/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-173983871107/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (2399912942647/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9601952741771/1000000000000:ℝ) := by nlinarith
  have hp1 : (15887410062257/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3178243675893/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2800815974033/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-552830620899/200000000000:ℝ) := by nlinarith
  have hN : (444851150107/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (22924374113801/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (444851150107/250000000000:ℝ) (22924374113801/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (941400597/10000000000000:ℝ) ≤ ((444851150107/250000000000:ℝ)/(22924374113801/125000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_290 (x : ℝ) (h₁ : (3129/1024:ℝ) ≤ x) (h₂ : x ≤ (25041/8192:ℝ)) : (940947087/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (874369049/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (891626333/5000000000:ℝ) := by nlinarith
  have hc1 : (984142137483/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (984142137483/1000000000000:ℝ) ≤ taylorCos (891626333/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (984748504067/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (874369049/5000000000:ℝ) + taylorErr ≤ (984748504067/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (173983871107/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (173983871107/1000000000000:ℝ) ≤ taylorSin (874369049/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (177381649501/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (891626333/5000000000:ℝ) + taylorErr ≤ (177381649501/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (-984142137483/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-177381649501/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-173983871107/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (2399912942647/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (4801551613681/500000000000:ℝ) := by nlinarith
  have hp1 : (15887410062257/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15893122431511/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2819148272623/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-552830620899/200000000000:ℝ) := by nlinarith
  have hN : (444851150107/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (183439183190741/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (444851150107/250000000000:ℝ) (183439183190741/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (940947087/10000000000000:ℝ) ≤ ((444851150107/250000000000:ℝ)/(183439183190741/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_291 (x : ℝ) (h₁ : (3129/1024:ℝ) ≤ x) (h₂ : x ≤ (6261/2048:ℝ)) : (18809877/200000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (874369049/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (897378761/5000000000:ℝ) := by nlinarith
  have hc1 : (61496088199/62500000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (61496088199/62500000000:ℝ) ≤ taylorCos (897378761/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (984748504067/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (874369049/5000000000:ℝ) + taylorErr ≤ (984748504067/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (173983871107/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (173983871107/1000000000000:ℝ) ≤ taylorSin (874369049/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (89256886609/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (897378761/5000000000:ℝ) + taylorErr ≤ (89256886609/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (-61496088199/62500000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-89256886609/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-173983871107/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (2399912942647/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1200531714119/125000000000:ℝ) := by nlinarith
  have hp1 : (15887410062257/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3973756620889/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-141874057649/50000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-552830620899/200000000000:ℝ) := by nlinarith
  have hN : (444851150107/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (36696675753101/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (444851150107/250000000000:ℝ) (36696675753101/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (18809877/200000000000:ℝ) ≤ ((444851150107/250000000000:ℝ)/(36696675753101/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_292 (x : ℝ) (h₁ : (3129/1024:ℝ) ≤ x) (h₂ : x ≤ (12525/4096:ℝ)) : (234897049/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (874369049/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (908883617/5000000000:ℝ) := by nlinarith
  have hc1 : (983524051789/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (983524051789/1000000000000:ℝ) ≤ taylorCos (908883617/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (984748504067/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (874369049/5000000000:ℝ) + taylorErr ≤ (984748504067/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (173983871107/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (173983871107/1000000000000:ℝ) ≤ taylorSin (874369049/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (5649290947/31250000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (908883617/5000000000:ℝ) + taylorErr ≤ (5649290947/31250000000:ℝ) := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (-983524051789/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-5649290947/31250000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-173983871107/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (2399912942647/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (4803277342067/500000000000:ℝ) := by nlinarith
  have hp1 : (15887410062257/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15898834587649/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-718537138431/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-552830620899/200000000000:ℝ) := by nlinarith
  have hN : (444851150107/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (91785892899257/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (444851150107/250000000000:ℝ) (91785892899257/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (234897049/2500000000000:ℝ) ≤ ((444851150107/250000000000:ℝ)/(91785892899257/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_293 (x : ℝ) (h₁ : (3129/1024:ℝ) ≤ x) (h₂ : x ≤ (783/256:ℝ)) : (469341817/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (874369049/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (920388473/5000000000:ℝ) := by nlinarith
  have hc1 : (983105485159/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (983105485159/1000000000000:ℝ) ≤ taylorCos (920388473/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (984748504067/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (874369049/5000000000:ℝ) + taylorErr ≤ (984748504067/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (173983871107/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (173983871107/1000000000000:ℝ) ≤ taylorSin (874369049/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (18303989027/100000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (920388473/5000000000:ℝ) + taylorErr ≤ (18303989027/100000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (-983105485159/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-18303989027/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-173983871107/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (2399912942647/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2402213913829/250000000000:ℝ) := by nlinarith
  have hp1 : (15887410062257/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (7951321345871/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-29108179733/10000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-552830620899/200000000000:ℝ) := by nlinarith
  have hN : (444851150107/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (183660214009397/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (444851150107/250000000000:ℝ) (183660214009397/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (469341817/5000000000000:ℝ) ≤ ((444851150107/250000000000:ℝ)/(183660214009397/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_294 (x : ℝ) (h₁ : (3129/1024:ℝ) ≤ x) (h₂ : x ≤ (6267/2048:ℝ)) : (37475111/400000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (874369049/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (188679637/1000000000:ℝ) := by nlinarith
  have hc1 : (982252739087/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (982252739087/1000000000000:ℝ) ≤ taylorCos (188679637/1000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (984748504067/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (874369049/5000000000:ℝ) + taylorErr ≤ (984748504067/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (173983871107/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (173983871107/1000000000000:ℝ) ≤ taylorSin (874369049/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (187562130933/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (188679637/1000000000:ℝ) + taylorErr ≤ (187562130933/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (-982252739087/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-187562130933/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-173983871107/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (2399912942647/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (120168219971/12500000000:ℝ) := by nlinarith
  have hp1 : (15887410062257/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15910258899929/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2984162062967/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-552830620899/200000000000:ℝ) := by nlinarith
  have hN : (444851150107/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (183837133964783/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (444851150107/250000000000:ℝ) (183837133964783/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (37475111/400000000000:ℝ) ≤ ((444851150107/250000000000:ℝ)/(183837133964783/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_295 (x : ℝ) (h₁ : (3129/1024:ℝ) ≤ x) (h₂ : x ≤ (3135/1024:ℝ)) : (935076261/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (874369049/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (1932815793/10000000000:ℝ) := by nlinarith
  have hc1 : (981379191047/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (981379191047/1000000000000:ℝ) ≤ taylorCos (1932815793/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (984748504067/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (874369049/5000000000:ℝ) + taylorErr ≤ (984748504067/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (173983871107/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (173983871107/1000000000000:ℝ) ≤ taylorSin (874369049/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (96040199669/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1932815793/10000000000:ℝ) + taylorErr ≤ (96040199669/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (-981379191047/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-96040199669/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-173983871107/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (2399912942647/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9618059540043/1000000000000:ℝ) := by nlinarith
  have hp1 : (15887410062257/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15917875108113/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-3057511807379/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-552830620899/200000000000:ℝ) := by nlinarith
  have hN : (444851150107/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (1472113109053/8000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (444851150107/250000000000:ℝ) (1472113109053/8000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (935076261/10000000000000:ℝ) ≤ ((444851150107/250000000000:ℝ)/(1472113109053/8000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_296 (x : ℝ) (h₁ : (3129/1024:ℝ) ≤ x) (h₂ : x ≤ (1569/512:ℝ)) : (46574311/500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (874369049/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (2024854641/10000000000:ℝ) := by nlinarith
  have hc1 : (979569763403/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (979569763403/1000000000000:ℝ) ≤ taylorCos (2024854641/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (984748504067/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (874369049/5000000000:ℝ) + taylorErr ≤ (984748504067/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (173983871107/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (173983871107/1000000000000:ℝ) ≤ taylorSin (874369049/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (201104637201/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2024854641/10000000000:ℝ) + taylorErr ≤ (201104637201/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (-979569763403/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-201104637201/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-173983871107/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (2399912942647/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (9627263424771/1000000000000:ℝ) := by nlinarith
  have hp1 : (15887410062257/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (7966553762243/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-3204221808197/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-552830620899/200000000000:ℝ) := by nlinarith
  have hN : (444851150107/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (184368402099867/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (444851150107/250000000000:ℝ) (184368402099867/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (46574311/500000000000:ℝ) ≤ ((444851150107/250000000000:ℝ)/(184368402099867/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_297 (x : ℝ) (h₁ : (25035/8192:ℝ) ≤ x) (h₂ : x ≤ (25041/8192:ℝ)) : (480324211/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (880121477/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (891626333/5000000000:ℝ) := by nlinarith
  have hc1 : (984142137483/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (984142137483/1000000000000:ℝ) ≤ taylorCos (891626333/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (123068460807/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (880121477/5000000000:ℝ) + taylorErr ≤ (123068460807/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (43779173671/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (43779173671/250000000000:ℝ) ≤ taylorSin (880121477/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (177381649501/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (891626333/5000000000:ℝ) + taylorErr ≤ (177381649501/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-123068460807/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-984142137483/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-177381649501/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-43779173671/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9600802256179/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (4801551613681/500000000000:ℝ) := by nlinarith
  have hp1 : (7944657057139/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (15893122431511/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2819148272623/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-347810521061/125000000000:ℝ) := by nlinarith
  have hN : (112371030127/62500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (183439183190741/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (112371030127/62500000000:ℝ) (183439183190741/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (480324211/5000000000000:ℝ) ≤ ((112371030127/62500000000:ℝ)/(183439183190741/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_298 (x : ℝ) (h₁ : (25035/8192:ℝ) ≤ x) (h₂ : x ≤ (6261/2048:ℝ)) : (192037139/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (880121477/5000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (897378761/5000000000:ℝ) := by nlinarith
  have hc1 : (61496088199/62500000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (61496088199/62500000000:ℝ) ≤ taylorCos (897378761/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (123068460807/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (880121477/5000000000:ℝ) + taylorErr ≤ (123068460807/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (43779173671/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (43779173671/250000000000:ℝ) ≤ taylorSin (880121477/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (89256886609/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (897378761/5000000000:ℝ) + taylorErr ≤ (89256886609/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-123068460807/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-61496088199/62500000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-89256886609/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-43779173671/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (9600802256179/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1200531714119/125000000000:ℝ) := by nlinarith
  have hp1 : (7944657057139/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3973756620889/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-141874057649/50000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-347810521061/125000000000:ℝ) := by nlinarith
  have hN : (112371030127/62500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (36696675753101/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (112371030127/62500000000:ℝ) (36696675753101/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (192037139/2000000000000:ℝ) ≤ ((112371030127/62500000000:ℝ)/(36696675753101/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_299 (x : ℝ) (h₁ : (12519/4096:ℝ) ≤ x) (h₂ : x ≤ (6261/2048:ℝ)) : (15313807/156250000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (177174781/1000000000:ℝ) ≤ Real.pi * (x - (3:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (3:ℝ)) ≤ (897378761/5000000000:ℝ) := by nlinarith
  have hc1 : (61496088199/62500000000:ℝ) ≤ Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (61496088199/62500000000:ℝ) ≤ taylorCos (897378761/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (3:ℝ))) ≤ (12304319571/12500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (177174781/1000000000:ℝ) + taylorErr ≤ (12304319571/12500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (176249286473/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (176249286473/1000000000000:ℝ) ≤ taylorSin (177174781/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (3:ℝ))) ≤ (89256886609/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (897378761/5000000000:ℝ) + taylorErr ≤ (89256886609/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).1
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (3:ℝ))) := by
    have h := (trig_shift (3:ℝ) (x - (3:ℝ))).2
    rw [show (3:ℝ) + (x - (3:ℝ)) = x by ring, cs_3.1, cs_3.2] at h
    rw [h]; ring
  have hcxl : (-12304319571/12500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-61496088199/62500000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-89256886609/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-176249286473/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (960195274177/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1200531714119/125000000000:ℝ) := by nlinarith
  have hp1 : (15891218166299/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3973756620889/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-141874057649/50000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-700203965749/250000000000:ℝ) := by nlinarith
  have hN : (454117574329/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (36696675753101/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (454117574329/250000000000:ℝ) (36696675753101/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (15313807/156250000000:ℝ) ≤ ((454117574329/250000000000:ℝ)/(36696675753101/200000000000:ℝ))^2 := by norm_num
  linarith

end Zeta23Ext.Bridge.ThreePoint
