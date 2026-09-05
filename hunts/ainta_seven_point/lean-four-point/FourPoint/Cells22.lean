import FourPoint.Base

noncomputable section
open Real
namespace Zeta23Ext.Bridge.FourPoint


theorem wc_1320 (x : ℝ) (h₁ : (10341/2048:ℝ) ≤ x) (h₂ : x ≤ (2603/512:ℝ)) : (1130887/31250000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (309864119/2000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (659611739/2500000000:ℝ) := by nlinarith
  have hc1 : (482697219707/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (482697219707/500000000000:ℝ) ≤ taylorCos (659611739/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (988022019417/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (309864119/2000000000:ℝ) + taylorErr ≤ (988022019417/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (6172518827/40000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (6172518827/40000000000:ℝ) ≤ taylorSin (309864119/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (130397060129/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (659611739/2500000000:ℝ) + taylorErr ≤ (130397060129/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-988022019417/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-482697219707/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-130397060129/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-6172518827/40000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (634515813101/40000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (7985903981733/500000000000:ℝ) := by nlinarith
  have hp1 : (525061385279/20000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3304164984563/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1723413600673/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-15824957451/3906250000:ℝ) := by nlinarith
  have hN : (3063167088039/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (63649662405459/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3063167088039/1000000000000:ℝ) (63649662405459/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1130887/31250000000:ℝ) ≤ ((3063167088039/1000000000000:ℝ)/(63649662405459/125000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1321 (x : ℝ) (h₁ : (10341/2048:ℝ) ≤ x) (h₂ : x ≤ (163/32:ℝ)) : (14364449/400000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (309864119/2000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2945243113/10000000000:ℝ) := by nlinarith
  have hc1 : (956940333463/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (956940333463/1000000000000:ℝ) ≤ taylorCos (2945243113/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (988022019417/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (309864119/2000000000:ℝ) + taylorErr ≤ (988022019417/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (6172518827/40000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (6172518827/40000000000:ℝ) ≤ taylorSin (309864119/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (290284679541/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2945243113/10000000000:ℝ) + taylorErr ≤ (290284679541/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-988022019417/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-956940333463/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-290284679541/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-6172518827/40000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (634515813101/40000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2000310947403/125000000000:ℝ) := by nlinarith
  have hp1 : (525061385279/20000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26484094597743/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-192198172831/25000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-15824957451/3906250000:ℝ) := by nlinarith
  have hN : (3063167088039/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (511159217446437/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3063167088039/1000000000000:ℝ) (511159217446437/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (14364449/400000000000:ℝ) ≤ ((3063167088039/1000000000000:ℝ)/(511159217446437/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1322 (x : ℝ) (h₁ : (10343/2048:ℝ) ≤ x) (h₂ : x ≤ (5207/1024:ℝ)) : (76188523/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1580000211/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2669126571/10000000000:ℝ) := by nlinarith
  have hc1 : (482294895513/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (482294895513/500000000000:ℝ) ≤ taylorCos (2669126571/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (197508788813/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1580000211/10000000000:ℝ) + taylorErr ≤ (197508788813/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (157343453303/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (157343453303/1000000000000:ℝ) ≤ taylorSin (1580000211/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (52750936249/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2669126571/10000000000:ℝ) + taylorErr ≤ (52750936249/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-197508788813/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-482294895513/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-52750936249/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-157343453303/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15865963289101/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (7987437962521/500000000000:ℝ) := by nlinarith
  have hp1 : (13129073368003/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (6609599337157/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-6973251065317/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-206577374239/50000000000:ℝ) := by nlinarith
  have hN : (628800708143/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (509393321640973/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (628800708143/200000000000:ℝ) (509393321640973/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (76188523/2000000000000:ℝ) ≤ ((628800708143/200000000000:ℝ)/(509393321640973/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1323 (x : ℝ) (h₁ : (10343/2048:ℝ) ≤ x) (h₂ : x ≤ (5217/1024:ℝ)) : (189012269/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1580000211/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2975922729/10000000000:ℝ) := by nlinarith
  have hc1 : (956045249073/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (956045249073/1000000000000:ℝ) ≤ taylorCos (2975922729/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (197508788813/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1580000211/10000000000:ℝ) + taylorErr ≤ (197508788813/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (157343453303/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (157343453303/1000000000000:ℝ) ≤ taylorSin (1580000211/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (73304791251/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2975922729/10000000000:ℝ) + taylorErr ≤ (73304791251/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-197508788813/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-956045249073/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-73304791251/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-157343453303/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15865963289101/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (16005555540799/1000000000000:ℝ) := by nlinarith
  have hp1 : (13129073368003/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5297834413973/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-3883566457987/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-206577374239/50000000000:ℝ) := by nlinarith
  have hN : (628800708143/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (127838904084801/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (628800708143/200000000000:ℝ) (127838904084801/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (189012269/5000000000000:ℝ) ≤ ((628800708143/200000000000:ℝ)/(127838904084801/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1324 (x : ℝ) (h₁ : (41373/8192:ℝ) ≤ x) (h₂ : x ≤ (5183/1024:ℝ)) : (390560199/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1583835163/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1932815793/10000000000:ℝ) := by nlinarith
  have hc1 : (981379191047/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (981379191047/1000000000000:ℝ) ≤ taylorCos (1932815793/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (246870882747/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1583835163/10000000000:ℝ) + taylorErr ≤ (246870882747/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (31544432017/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (31544432017/200000000000:ℝ) ≤ taylorSin (1583835163/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (96040199669/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1932815793/10000000000:ℝ) + taylorErr ≤ (96040199669/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-246870882747/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-981379191047/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-96040199669/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-31544432017/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7933173392149/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15901244847223/1000000000000:ℝ) := by nlinarith
  have hp1 : (26258781420013/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3289567252207/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2527445565813/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1035397931691/250000000000:ℝ) := by nlinarith
  have hN : (49282940559/15625000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (504699175382673/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (49282940559/15625000000:ℝ) (504699175382673/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (390560199/10000000000000:ℝ) ≤ ((49282940559/15625000000:ℝ)/(504699175382673/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1325 (x : ℝ) (h₁ : (10345/2048:ℝ) ≤ x) (h₂ : x ≤ (1295/256:ℝ)) : (102305567/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1610679827/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (920388473/5000000000:ℝ) := by nlinarith
  have hc1 : (983105485159/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (983105485159/1000000000000:ℝ) ≤ taylorCos (920388473/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (246764143393/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1610679827/10000000000:ℝ) + taylorErr ≤ (246764143393/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (160372454953/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (160372454953/1000000000000:ℝ) ≤ taylorSin (1610679827/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (18303989027/100000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (920388473/5000000000:ℝ) + taylorErr ≤ (18303989027/100000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-246764143393/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-983105485159/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-18303989027/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-160372454953/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3967257812669/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (248313140039/15625000000:ℝ) := by nlinarith
  have hp1 : (26263224208061/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5260261120257/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-4814188091217/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-4211897741227/1000000000000:ℝ) := by nlinarith
  have hN : (644968233531/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (252056965953651/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (644968233531/200000000000:ℝ) (252056965953651/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (102305567/2500000000000:ℝ) ≤ ((644968233531/200000000000:ℝ)/(252056965953651/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1326 (x : ℝ) (h₁ : (10345/2048:ℝ) ≤ x) (h₂ : x ≤ (10365/2048:ℝ)) : (408431653/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1610679827/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (383495197/2000000000:ℝ) := by nlinarith
  have hc1 : (245418170983/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (245418170983/250000000000:ℝ) ≤ taylorCos (383495197/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (246764143393/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1610679827/10000000000:ℝ) + taylorErr ≤ (246764143393/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (160372454953/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (160372454953/1000000000000:ℝ) ≤ taylorSin (1610679827/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (23821844637/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (383495197/2000000000:ℝ) + taylorErr ≤ (23821844637/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-246764143393/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-245418170983/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-23821844637/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-160372454953/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3967257812669/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3179942173287/200000000000:ℝ) := by nlinarith
  have hp1 : (26263224208061/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13156999640797/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1002956804263/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-4211897741227/1000000000000:ℝ) := by nlinarith
  have hN : (644968233531/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (504601611272463/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (644968233531/200000000000:ℝ) (504601611272463/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (408431653/10000000000000:ℝ) ≤ ((644968233531/200000000000:ℝ)/(504601611272463/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1327 (x : ℝ) (h₁ : (10345/2048:ℝ) ≤ x) (h₂ : x ≤ (5185/1024:ℝ)) : (407642947/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1610679827/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (79767001/400000000:ℝ) := by nlinarith
  have hc1 : (980182133691/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (980182133691/1000000000000:ℝ) ≤ taylorCos (79767001/400000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (246764143393/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1610679827/10000000000:ℝ) + taylorErr ≤ (246764143393/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (160372454953/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (160372454953/1000000000000:ℝ) ≤ taylorSin (1610679827/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (198098413053/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (79767001/400000000:ℝ) + taylorErr ≤ (198098413053/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-246764143393/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-980182133691/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-198098413053/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-160372454953/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3967257812669/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (127259046163/8000000000:ℝ) := by nlinarith
  have hp1 : (26263224208061/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5265338592381/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-5215276096687/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-4211897741227/1000000000000:ℝ) := by nlinarith
  have hN : (644968233531/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (505089525947393/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (644968233531/200000000000:ℝ) (505089525947393/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (407642947/10000000000000:ℝ) ≤ ((644968233531/200000000000:ℝ)/(505089525947393/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1328 (x : ℝ) (h₁ : (20691/4096:ℝ) ≤ x) (h₂ : x ≤ (41473/8192:ℝ)) : (82609501/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1618349731/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1967330361/10000000000:ℝ) := by nlinarith
  have hc1 : (98071038981/100000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (98071038981/100000000000:ℝ) ≤ taylorCos (1967330361/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (986933279119/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1618349731/10000000000:ℝ) + taylorErr ≤ (986933279119/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (80564735311/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (80564735311/500000000000:ℝ) ≤ taylorSin (1618349731/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (9773321821/50000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1967330361/10000000000:ℝ) + taylorErr ≤ (9773321821/50000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-986933279119/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-98071038981/100000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-9773321821/50000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-80564735311/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1586979824107/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3976174075999/250000000000:ℝ) := by nlinarith
  have hp1 : (1050579743043/40000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (6580562543449/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1286279110007/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-4231983946067/1000000000000:ℝ) := by nlinarith
  have hN : (811262666737/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (504918729044689/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (811262666737/250000000000:ℝ) (504918729044689/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (82609501/2000000000000:ℝ) ≤ ((811262666737/250000000000:ℝ)/(504918729044689/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1329 (x : ℝ) (h₁ : (20691/4096:ℝ) ≤ x) (h₂ : x ≤ (41493/8192:ℝ)) : (51531267/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1618349731/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (10220147/50000000:ℝ) := by nlinarith
  have hc1 : (19583646991/20000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (19583646991/20000000000:ℝ) ≤ taylorCos (10220147/50000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (986933279119/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1618349731/10000000000:ℝ) + taylorErr ≤ (986933279119/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (80564735311/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (80564735311/500000000000:ℝ) ≤ taylorSin (1618349731/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (101491283883/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (10220147/50000000:ℝ) + taylorErr ≤ (101491283883/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-986933279119/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-19583646991/20000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-101491283883/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-80564735311/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1586979824107/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3182473241587/200000000000:ℝ) := by nlinarith
  have hp1 : (1050579743043/40000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5266988770821/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-133638363137/25000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-4231983946067/1000000000000:ℝ) := by nlinarith
  have hN : (811262666737/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (31587924791929/62500000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (811262666737/250000000000:ℝ) (31587924791929/62500000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (51531267/1250000000000:ℝ) ≤ ((811262666737/250000000000:ℝ)/(31587924791929/62500000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1330 (x : ℝ) (h₁ : (20693/4096:ℝ) ≤ x) (h₂ : x ≤ (5191/1024:ℝ)) : (421158101/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1633689539/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2178252719/10000000000:ℝ) := by nlinarith
  have hc1 : (976369729063/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (976369729063/1000000000000:ℝ) ≤ taylorCos (2178252719/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (246671237131/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1633689539/10000000000:ℝ) + taylorErr ≤ (246671237131/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (162643217149/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (162643217149/1000000000000:ℝ) ≤ taylorSin (1633689539/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (108053399679/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2178252719/10000000000:ℝ) + taylorErr ≤ (108053399679/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-246671237131/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-976369729063/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-108053399679/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-162643217149/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7935666110929/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15925788539829/1000000000000:ℝ) := by nlinarith
  have hp1 : (26267032312103/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13178578897323/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-227838440447/40000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-4272154640197/1000000000000:ℝ) := by nlinarith
  have hN : (3285469691673/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (253130740615349/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3285469691673/1000000000000:ℝ) (253130740615349/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (421158101/10000000000000:ℝ) ≤ ((3285469691673/1000000000000:ℝ)/(253130740615349/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1331 (x : ℝ) (h₁ : (20695/4096:ℝ) ≤ x) (h₂ : x ≤ (10403/2048:ℝ)) : (214051577/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (824514673/5000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (500077737/2000000000:ℝ) := by nlinarith
  have hc1 : (15139106289/15625000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (15139106289/15625000000:ℝ) ≤ taylorCos (500077737/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (49321714809/50000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (824514673/5000000000:ℝ) + taylorErr ≤ (49321714809/50000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (82078290431/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (82078290431/500000000000:ℝ) ≤ taylorSin (824514673/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (123720810751/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (500077737/2000000000:ℝ) + taylorErr ≤ (123720810751/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-49321714809/50000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-15139106289/15625000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-123720810751/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-82078290431/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7936433101323/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (127664017091/8000000000:ℝ) := by nlinarith
  have hp1 : (26269571048131/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26410471251947/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-3267524915607/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1078080740993/250000000000:ℝ) := by nlinarith
  have hN : (207868041737/62500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (508315664369099/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (207868041737/62500000000:ℝ) (508315664369099/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (214051577/5000000000000:ℝ) ≤ ((207868041737/62500000000:ℝ)/(508315664369099/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1332 (x : ℝ) (h₁ : (41391/8192:ℝ) ≤ x) (h₂ : x ≤ (20751/4096:ℝ)) : (10882551/250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (826432149/5000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (64954499/312500000:ℝ) := by nlinarith
  have hc1 : (97847593311/100000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (97847593311/100000000000:ℝ) ≤ taylorCos (64954499/312500000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (986371270383/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (826432149/5000000000:ℝ) + taylorErr ≤ (986371270383/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (164534861599/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (164534861599/1000000000000:ℝ) ≤ taylorSin (826432149/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (25795119703/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (64954499/312500000:ℝ) + taylorErr ≤ (25795119703/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-986371270383/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-97847593311/100000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-25795119703/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-164534861599/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15873249697843/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3978954416177/250000000000:ℝ) := by nlinarith
  have hp1 : (13135102866069/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (6585164002561/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-5435682998719/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2161182332157/500000000000:ℝ) := by nlinarith
  have hN : (3335993393931/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (505626503872463/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3335993393931/1000000000000:ℝ) (505626503872463/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (10882551/250000000000:ℝ) ≤ ((3335993393931/1000000000000:ℝ)/(505626503872463/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1333 (x : ℝ) (h₁ : (41393/8192:ℝ) ≤ x) (h₂ : x ≤ (10371/2048:ℝ)) : (110339709/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (830267101/5000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2009514833/10000000000:ℝ) := by nlinarith
  have hc1 : (48993855071/50000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (48993855071/50000000000:ℝ) ≤ taylorCos (2009514833/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (493122391803/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (830267101/5000000000:ℝ) + taylorErr ≤ (493122391803/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (82645675211/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (82645675211/500000000000:ℝ) ≤ taylorSin (830267101/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (199601759969/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2009514833/10000000000:ℝ) + taylorErr ≤ (199601759969/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-493122391803/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-48993855071/50000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-199601759969/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-82645675211/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15874016688237/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (7954457375581/500000000000:ℝ) := by nlinarith
  have hp1 : (3283934387519/125000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5265846339593/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2627680492773/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2171223798441/500000000000:ℝ) := by nlinarith
  have hN : (839050703319/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (12629678427987/25000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (839050703319/250000000000:ℝ) (12629678427987/25000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (110339709/2500000000000:ℝ) ≤ ((839050703319/250000000000:ℝ)/(12629678427987/25000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1334 (x : ℝ) (h₁ : (41395/8192:ℝ) ≤ x) (h₂ : x ≤ (20753/4096:ℝ)) : (222870971/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (834102053/5000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (16358467/78125000:ℝ) := by nlinarith
  have hc1 : (489079114133/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (489079114133/500000000000:ℝ) ≤ taylorCos (16358467/78125000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (493058858323/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (834102053/5000000000:ℝ) + taylorErr ≤ (493058858323/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (166047742009/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (166047742009/1000000000000:ℝ) ≤ taylorSin (834102053/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (10393083877/50000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (16358467/78125000:ℝ) + taylorErr ≤ (10393083877/50000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-493058858323/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-489079114133/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-10393083877/50000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-166047742009/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15874783678631/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1989668955687/125000000000:ℝ) := by nlinarith
  have hp1 : (13136372234083/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26343194746307/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-5475740651731/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2181264947659/500000000000:ℝ) := by nlinarith
  have hN : (211025761167/62500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (505724166812749/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (211025761167/62500000000:ℝ) (505724166812749/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (222870971/5000000000000:ℝ) ≤ ((211025761167/62500000000:ℝ)/(505724166812749/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1335 (x : ℝ) (h₁ : (5175/1024:ℝ) ≤ x) (h₂ : x ≤ (10365/2048:ℝ)) : (115306701/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (843689433/5000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (383495197/2000000000:ℝ) := by nlinarith
  have hc1 : (245418170983/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (245418170983/250000000000:ℝ) ≤ taylorCos (383495197/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (985797511441/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (843689433/5000000000:ℝ) + taylorErr ≤ (985797511441/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (83969146323/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (83969146323/500000000000:ℝ) ≤ taylorSin (843689433/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (23821844637/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (383495197/2000000000:ℝ) + taylorErr ≤ (23821844637/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-985797511441/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-245418170983/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-23821844637/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-83969146323/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1984587644327/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3179942173287/200000000000:ℝ) := by nlinarith
  have hp1 : (26275917888201/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13156999640797/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1002956804263/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-88254655757/20000000000:ℝ) := by nlinarith
  have hN : (3426935276409/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (504601611272463/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3426935276409/1000000000000:ℝ) (504601611272463/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (115306701/2500000000000:ℝ) ≤ ((3426935276409/1000000000000:ℝ)/(504601611272463/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1336 (x : ℝ) (h₁ : (5175/1024:ℝ) ≤ x) (h₂ : x ≤ (5185/1024:ℝ)) : (460336147/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (843689433/5000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (79767001/400000000:ℝ) := by nlinarith
  have hc1 : (980182133691/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (980182133691/1000000000000:ℝ) ≤ taylorCos (79767001/400000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (985797511441/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (843689433/5000000000:ℝ) + taylorErr ≤ (985797511441/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (83969146323/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (83969146323/500000000000:ℝ) ≤ taylorSin (843689433/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (198098413053/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (79767001/400000000:ℝ) + taylorErr ≤ (198098413053/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-985797511441/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-980182133691/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-198098413053/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-83969146323/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1984587644327/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (127259046163/8000000000:ℝ) := by nlinarith
  have hp1 : (26275917888201/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5265338592381/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-5215276096687/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-88254655757/20000000000:ℝ) := by nlinarith
  have hN : (3426935276409/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (505089525947393/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3426935276409/1000000000000:ℝ) (505089525947393/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (460336147/10000000000000:ℝ) ≤ ((3426935276409/1000000000000:ℝ)/(505089525947393/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1337 (x : ℝ) (h₁ : (5175/1024:ℝ) ≤ x) (h₂ : x ≤ (10375/2048:ℝ)) : (11486191/250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (843689433/5000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (129429629/625000000:ℝ) := by nlinarith
  have hc1 : (12232924027/12500000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (12232924027/12500000000:ℝ) ≤ taylorCos (129429629/625000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (985797511441/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (843689433/5000000000:ℝ) + taylorErr ≤ (985797511441/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (83969146323/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (83969146323/500000000000:ℝ) ≤ taylorSin (843689433/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (4112208307/20000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (129429629/625000000:ℝ) + taylorErr ≤ (4112208307/20000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-985797511441/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-12232924027/12500000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-4112208307/20000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-83969146323/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1984587644327/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (7957525337157/500000000000:ℝ) := by nlinarith
  have hp1 : (26275917888201/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26339386642213/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-541565222757/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-88254655757/20000000000:ℝ) := by nlinarith
  have hN : (3426935276409/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (252788837965983/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3426935276409/1000000000000:ℝ) (252788837965983/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (11486191/250000000000:ℝ) ≤ ((3426935276409/1000000000000:ℝ)/(252788837965983/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1338 (x : ℝ) (h₁ : (5175/1024:ℝ) ≤ x) (h₂ : x ≤ (2595/512:ℝ)) : (458561277/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (843689433/5000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (134223319/625000000:ℝ) := by nlinarith
  have hc1 : (7816225123/8000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (7816225123/8000000000:ℝ) ≤ taylorCos (134223319/625000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (985797511441/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (843689433/5000000000:ℝ) + taylorErr ≤ (985797511441/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (83969146323/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (83969146323/500000000000:ℝ) ≤ taylorSin (843689433/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (6659697571/31250000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (134223319/625000000:ℝ) + taylorErr ≤ (6659697571/31250000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-985797511441/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-7816225123/8000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-6659697571/31250000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-83969146323/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1984587644327/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15922720578253/1000000000000:ℝ) := by nlinarith
  have hp1 : (26275917888201/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13176040161261/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-5615900330071/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-88254655757/20000000000:ℝ) := by nlinarith
  have hN : (3426935276409/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (126516515306561/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3426935276409/1000000000000:ℝ) (126516515306561/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (458561277/10000000000000:ℝ) ≤ ((3426935276409/1000000000000:ℝ)/(126516515306561/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1339 (x : ℝ) (h₁ : (5175/1024:ℝ) ≤ x) (h₂ : x ≤ (20771/4096:ℝ)) : (228794373/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (843689433/5000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2231942047/10000000000:ℝ) := by nlinarith
  have hc1 : (975195399657/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (975195399657/1000000000000:ℝ) ≤ taylorCos (2231942047/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (985797511441/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (843689433/5000000000:ℝ) + taylorErr ≤ (985797511441/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (83969146323/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (83969146323/500000000000:ℝ) ≤ taylorSin (843689433/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (22134572297/100000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2231942047/10000000000:ℝ) + taylorErr ≤ (22134572297/100000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-985797511441/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-975195399657/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-22134572297/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-83969146323/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1984587644327/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15931157472587/1000000000000:ℝ) := by nlinarith
  have hp1 : (26275917888201/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1647877710679/62500000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-5836010931783/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-88254655757/20000000000:ℝ) := by nlinarith
  have hN : (3426935276409/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (50660355683273/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3426935276409/1000000000000:ℝ) (50660355683273/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (228794373/5000000000000:ℝ) ≤ ((3426935276409/1000000000000:ℝ)/(50660355683273/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1340 (x : ℝ) (h₁ : (5175/1024:ℝ) ≤ x) (h₂ : x ≤ (5195/1024:ℝ)) : (114198739/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (843689433/5000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1150485591/5000000000:ℝ) := by nlinarith
  have hc1 : (194728849477/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (194728849477/200000000000:ℝ) ≤ taylorCos (1150485591/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (985797511441/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (843689433/5000000000:ℝ) + taylorErr ≤ (985797511441/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (83969146323/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (83969146323/500000000000:ℝ) ≤ taylorSin (843689433/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (4561441709/20000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1150485591/5000000000:ℝ) + taylorErr ≤ (4561441709/20000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-985797511441/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-194728849477/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-4561441709/20000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-83969146323/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1984587644327/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3984515096533/250000000000:ℝ) := by nlinarith
  have hp1 : (26275917888201/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26377467683141/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-751995507923/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-88254655757/20000000000:ℝ) := by nlinarith
  have hN : (3426935276409/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (507043537743981/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3426935276409/1000000000000:ℝ) (507043537743981/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (114198739/2500000000000:ℝ) ≤ ((3426935276409/1000000000000:ℝ)/(507043537743981/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1341 (x : ℝ) (h₁ : (5175/1024:ℝ) ≤ x) (h₂ : x ≤ (325/64:ℝ)) : (91007427/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (843689433/5000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2454369261/10000000000:ℝ) := by nlinarith
  have hc1 : (970031250923/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (970031250923/1000000000000:ℝ) ≤ taylorCos (2454369261/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (985797511441/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (843689433/5000000000:ℝ) + taylorErr ≤ (985797511441/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (83969146323/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (83969146323/500000000000:ℝ) ≤ taylorSin (843689433/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (242980182203/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2454369261/10000000000:ℝ) + taylorErr ≤ (242980182203/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-985797511441/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-970031250923/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-242980182203/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-83969146323/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1984587644327/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15953400194011/1000000000000:ℝ) := by nlinarith
  have hp1 : (26275917888201/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26402855043761/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-6415370529213/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-88254655757/20000000000:ℝ) := by nlinarith
  have hN : (3426935276409/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (508021955500541/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3426935276409/1000000000000:ℝ) (508021955500541/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (91007427/2000000000000:ℝ) ≤ ((3426935276409/1000000000000:ℝ)/(508021955500541/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1342 (x : ℝ) (h₁ : (5175/1024:ℝ) ≤ x) (h₂ : x ≤ (20811/4096:ℝ)) : (227036969/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (843689433/5000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (634684551/2500000000:ℝ) := by nlinarith
  have hc1 : (483973376683/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (483973376683/500000000000:ℝ) ≤ taylorCos (634684551/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (985797511441/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (843689433/5000000000:ℝ) + taylorErr ≤ (985797511441/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (83969146323/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (83969146323/500000000000:ℝ) ≤ taylorSin (843689433/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (50231097701/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (634684551/2500000000:ℝ) + taylorErr ≤ (50231097701/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-985797511441/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-483973376683/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-50231097701/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-83969146323/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1984587644327/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3192367417669/200000000000:ℝ) := by nlinarith
  have hp1 : (26275917888201/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13208409046051/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-663472885267/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-88254655757/20000000000:ℝ) := by nlinarith
  have hN : (3426935276409/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (127140121617433/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3426935276409/1000000000000:ℝ) (127140121617433/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (227036969/5000000000000:ℝ) ≤ ((3426935276409/1000000000000:ℝ)/(127140121617433/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1343 (x : ℝ) (h₁ : (5175/1024:ℝ) ≤ x) (h₂ : x ≤ (2623/512:ℝ)) : (439255509/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (843689433/5000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1932815793/5000000000:ℝ) := by nlinarith
  have hc1 : (57888139991/62500000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (57888139991/62500000000:ℝ) ≤ taylorCos (1932815793/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (985797511441/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (843689433/5000000000:ℝ) + taylorErr ≤ (985797511441/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (83969146323/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (83969146323/500000000000:ℝ) ≤ taylorSin (843689433/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (377007412527/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1932815793/5000000000:ℝ) + taylorErr ≤ (377007412527/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-985797511441/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-57888139991/62500000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-377007412527/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-83969146323/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1984587644327/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (16094526426497/1000000000000:ℝ) := by nlinarith
  have hp1 : (26275917888201/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1664776172591/62500000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-10042127316243/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-88254655757/20000000000:ℝ) := by nlinarith
  have hN : (3426935276409/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (517067561786421/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3426935276409/1000000000000:ℝ) (517067561786421/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (439255509/10000000000000:ℝ) ≤ ((3426935276409/1000000000000:ℝ)/(517067561786421/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1344 (x : ℝ) (h₁ : (5175/1024:ℝ) ≤ x) (h₂ : x ≤ (2633/512:ℝ)) : (432607663/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (843689433/5000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (4479223901/10000000000:ℝ) := by nlinarith
  have hc1 : (28167151399/31250000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (28167151399/31250000000:ℝ) ≤ taylorCos (4479223901/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (985797511441/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (843689433/5000000000:ℝ) + taylorErr ≤ (985797511441/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (83969146323/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (83969146323/500000000000:ℝ) ≤ taylorSin (843689433/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (433093821149/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (4479223901/10000000000:ℝ) + taylorErr ≤ (433093821149/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-985797511441/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-28167151399/31250000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-433093821149/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-83969146323/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1984587644327/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (4038971414503/250000000000:ℝ) := by nlinarith
  have hp1 : (26275917888201/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (6684492050983/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-5790024409601/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-88254655757/20000000000:ℝ) := by nlinarith
  have hN : (3426935276409/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (130256320697379/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3426935276409/1000000000000:ℝ) (130256320697379/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (432607663/10000000000000:ℝ) ≤ ((3426935276409/1000000000000:ℝ)/(130256320697379/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1345 (x : ℝ) (h₁ : (20701/4096:ℝ) ≤ x) (h₂ : x ≤ (41493/8192:ℝ)) : (465196871/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (169504877/1000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (10220147/50000000:ℝ) := by nlinarith
  have hc1 : (19583646991/20000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (19583646991/20000000000:ℝ) ≤ taylorCos (10220147/50000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (492834207217/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (169504877/1000000000:ℝ) + taylorErr ≤ (492834207217/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (168694340401/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (168694340401/1000000000000:ℝ) ≤ taylorSin (169504877/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (101491283883/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (10220147/50000000:ℝ) + taylorErr ≤ (101491283883/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-492834207217/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-19583646991/20000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-101491283883/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-168694340401/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1587746814501/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3182473241587/200000000000:ℝ) := by nlinarith
  have hp1 : (5255437451243/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5266988770821/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-133638363137/25000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-221640638589/50000000000:ℝ) := by nlinarith
  have hN : (1723572178673/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (31587924791929/62500000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1723572178673/500000000000:ℝ) (31587924791929/62500000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (465196871/10000000000000:ℝ) ≤ ((1723572178673/500000000000:ℝ)/(31587924791929/62500000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1346 (x : ℝ) (h₁ : (10351/2048:ℝ) ≤ x) (h₂ : x ≤ (41495/8192:ℝ)) : (235288201/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (851359337/5000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (256462413/1250000000:ℝ) := by nlinarith
  have hc1 : (979026375873/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (979026375873/1000000000000:ℝ) ≤ taylorCos (256462413/1250000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (61596171099/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (851359337/5000000000:ℝ) + taylorErr ≤ (61596171099/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (169450288917/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (169450288917/1000000000000:ℝ) ≤ taylorSin (851359337/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (50933382863/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (256462413/1250000000:ℝ) + taylorErr ≤ (50933382863/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-61596171099/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-979026375873/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-50933382863/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-169450288917/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3969558783851/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15913133198329/1000000000000:ℝ) := by nlinarith
  have hp1 : (26278456624229/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3292026652767/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-5365569724819/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1113223016817/250000000000:ℝ) := by nlinarith
  have hN : (866838332421/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (252727808187761/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (866838332421/250000000000:ℝ) (252727808187761/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (235288201/5000000000000:ℝ) ≤ ((866838332421/250000000000:ℝ)/(252727808187761/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1347 (x : ℝ) (h₁ : (10351/2048:ℝ) ≤ x) (h₂ : x ≤ (20773/4096:ℝ)) : (234132737/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (851359337/5000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (449456371/2000000000:ℝ) := by nlinarith
  have hc1 : (48742735617/50000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (48742735617/50000000000:ℝ) ≤ taylorCos (449456371/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (61596171099/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (851359337/5000000000:ℝ) + taylorErr ≤ (61596171099/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (169450288917/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (169450288917/1000000000000:ℝ) ≤ taylorSin (851359337/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (111420696491/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (449456371/2000000000:ℝ) + taylorErr ≤ (111420696491/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-61596171099/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-48742735617/50000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-111420696491/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-169450288917/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3969558783851/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (127461531627/8000000000:ℝ) := by nlinarith
  have hp1 : (26278456624229/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13184291053463/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1469002891917/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1113223016817/250000000000:ℝ) := by nlinarith
  have hN : (866838332421/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (253350656948449/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (866838332421/250000000000:ℝ) (253350656948449/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (234132737/5000000000000:ℝ) ≤ ((866838332421/250000000000:ℝ)/(253350656948449/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1348 (x : ℝ) (h₁ : (10351/2048:ℝ) ≤ x) (h₂ : x ≤ (20793/4096:ℝ)) : (58307863/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (851359337/5000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1200339967/5000000000:ℝ) := by nlinarith
  have hc1 : (194264361627/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (194264361627/200000000000:ℝ) ≤ taylorCos (1200339967/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (61596171099/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (851359337/5000000000:ℝ) + taylorErr ≤ (61596171099/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (169450288917/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (169450288917/1000000000000:ℝ) ≤ taylorSin (851359337/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (237768672711/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1200339967/5000000000:ℝ) + taylorErr ≤ (237768672711/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-61596171099/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-194264361627/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-237768672711/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-169450288917/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3969558783851/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (7974015630627/500000000000:ℝ) := by nlinarith
  have hp1 : (26278456624229/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5278793893509/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-6275659087873/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1113223016817/250000000000:ℝ) := by nlinarith
  have hN : (866838332421/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (50767940221987/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (866838332421/250000000000:ℝ) (50767940221987/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (58307863/1250000000000:ℝ) ≤ ((866838332421/250000000000:ℝ)/(50767940221987/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1349 (x : ℝ) (h₁ : (647/128:ℝ) ≤ x) (h₂ : x ≤ (20795/4096:ℝ)) : (238608519/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (859029241/5000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2416019741/10000000000:ℝ) := by nlinarith
  have hc1 : (970955932919/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (970955932919/1000000000000:ℝ) ≤ taylorCos (2416019741/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (492638822329/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (859029241/5000000000:ℝ) + taylorErr ≤ (492638822329/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (21370235807/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (21370235807/125000000000:ℝ) ≤ taylorSin (859029241/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (239258381291/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2416019741/10000000000:ℝ) + taylorErr ≤ (239258381291/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-492638822329/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-970955932919/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-239258381291/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-21370235807/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (496242784881/31250000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15949565242041/1000000000000:ℝ) := by nlinarith
  have hp1 : (26280995360257/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5279301640721/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-631558582453/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-449304854473/100000000000:ℝ) := by nlinarith
  have hN : (438471362509/125000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (101555452564049/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (438471362509/125000000000:ℝ) (101555452564049/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (238608519/5000000000000:ℝ) ≤ ((438471362509/125000000000:ℝ)/(101555452564049/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1350 (x : ℝ) (h₁ : (647/128:ℝ) ≤ x) (h₂ : x ≤ (10423/2048:ℝ)) : (236277491/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (859029241/5000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1403592421/5000000000:ℝ) := by nlinarith
  have hc1 : (960856630841/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (960856630841/1000000000000:ℝ) ≤ taylorCos (1403592421/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (492638822329/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (859029241/5000000000:ℝ) + taylorErr ≤ (492638822329/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (21370235807/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (21370235807/125000000000:ℝ) ≤ taylorSin (859029241/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (55409216517/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1403592421/5000000000:ℝ) + taylorErr ≤ (55409216517/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-492638822329/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-960856630841/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-55409216517/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-21370235807/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (496242784881/31250000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15988681752133/1000000000000:ℝ) := by nlinarith
  have hp1 : (26280995360257/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5292249194637/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-733098453719/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-449304854473/100000000000:ℝ) := by nlinarith
  have hN : (438471362509/125000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (255137944170991/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (438471362509/125000000000:ℝ) (255137944170991/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (236277491/5000000000000:ℝ) ≤ ((438471362509/125000000000:ℝ)/(255137944170991/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1351 (x : ℝ) (h₁ : (41413/8192:ℝ) ≤ x) (h₂ : x ≤ (10371/2048:ℝ)) : (496110717/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (868616621/5000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2009514833/10000000000:ℝ) := by nlinarith
  have hc1 : (48993855071/50000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (48993855071/50000000000:ℝ) ≤ taylorCos (2009514833/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (984948018249/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (868616621/5000000000:ℝ) + taylorErr ≤ (984948018249/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (86425408621/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (86425408621/500000000000:ℝ) ≤ taylorSin (868616621/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (199601759969/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2009514833/10000000000:ℝ) + taylorErr ≤ (199601759969/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-984948018249/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-48993855071/50000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-199601759969/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-86425408621/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15881686592177/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (7954457375581/500000000000:ℝ) := by nlinarith
  have hp1 : (6571042195073/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5265846339593/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2627680492773/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-22716200271/5000000000:ℝ) := by nlinarith
  have hN : (3558292035951/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (12629678427987/25000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3558292035951/1000000000000:ℝ) (12629678427987/25000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (496110717/10000000000000:ℝ) ≤ ((3558292035951/1000000000000:ℝ)/(12629678427987/25000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1352 (x : ℝ) (h₁ : (41413/8192:ℝ) ≤ x) (h₂ : x ≤ (10381/2048:ℝ)) : (494198099/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (868616621/5000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2162912911/10000000000:ℝ) := by nlinarith
  have hc1 : (195340016773/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (195340016773/200000000000:ℝ) ≤ taylorCos (2162912911/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (984948018249/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (868616621/5000000000:ℝ) + taylorErr ≤ (984948018249/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (86425408621/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (86425408621/500000000000:ℝ) ≤ taylorSin (868616621/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (13413050829/62500000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2162912911/10000000000:ℝ) + taylorErr ≤ (13413050829/62500000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-984948018249/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-195340016773/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-13413050829/62500000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-86425408621/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15881686592177/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15924254559041/1000000000000:ℝ) := by nlinarith
  have hp1 : (6571042195073/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3294327382323/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1413983380047/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-22716200271/5000000000:ℝ) := by nlinarith
  have hN : (3558292035951/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (506163766522277/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3558292035951/1000000000000:ℝ) (506163766522277/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (494198099/10000000000000:ℝ) ≤ ((3558292035951/1000000000000:ℝ)/(506163766522277/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1353 (x : ℝ) (h₁ : (5177/1024:ℝ) ≤ x) (h₂ : x ≤ (41/8:ℝ)) : (480942433/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (874369049/5000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (3926990817/10000000000:ℝ) := by nlinarith
  have hc1 : (923879530249/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (923879530249/1000000000000:ℝ) ≤ taylorCos (3926990817/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (984748504067/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (874369049/5000000000:ℝ) + taylorErr ≤ (984748504067/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (173983871107/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (173983871107/1000000000000:ℝ) ≤ taylorSin (874369049/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (95670858657/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/10000000000:ℝ) + taylorErr ≤ (95670858657/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-984748504067/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-923879530249/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-95670858657/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-173983871107/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15882837077767/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1006291396853/62500000000:ℝ) := by nlinarith
  have hp1 : (26286072832311/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26646573705703/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-10197202346767/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2286676353783/500000000000:ℝ) := by nlinarith
  have hN : (3588604203499/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (258731328097373/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3588604203499/1000000000000:ℝ) (258731328097373/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (480942433/10000000000000:ℝ) ≤ ((3588604203499/1000000000000:ℝ)/(258731328097373/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1354 (x : ℝ) (h₁ : (10355/2048:ℝ) ≤ x) (h₂ : x ≤ (10375/2048:ℝ)) : (103046413/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (882038953/5000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (129429629/625000000:ℝ) := by nlinarith
  have hc1 : (12232924027/12500000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (12232924027/12500000000:ℝ) ≤ taylorCos (129429629/625000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (984480457647/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (882038953/5000000000:ℝ) + taylorErr ≤ (984480457647/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (43873562777/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (43873562777/250000000000:ℝ) ≤ taylorSin (882038953/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (4112208307/20000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (129429629/625000000:ℝ) + taylorErr ≤ (4112208307/20000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-984480457647/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-12232924027/12500000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-4112208307/20000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-43873562777/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3176874211711/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (7957525337157/500000000000:ℝ) := by nlinarith
  have hp1 : (26288611568339/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26339386642213/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-541565222757/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2306750099927/500000000000:ℝ) := by nlinarith
  have hN : (3629019742207/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (252788837965983/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3629019742207/1000000000000:ℝ) (252788837965983/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (103046413/2000000000000:ℝ) ≤ ((3629019742207/1000000000000:ℝ)/(252788837965983/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1355 (x : ℝ) (h₁ : (10355/2048:ℝ) ≤ x) (h₂ : x ≤ (2595/512:ℝ)) : (257119041/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (882038953/5000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (134223319/625000000:ℝ) := by nlinarith
  have hc1 : (7816225123/8000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (7816225123/8000000000:ℝ) ≤ taylorCos (134223319/625000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (984480457647/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (882038953/5000000000:ℝ) + taylorErr ≤ (984480457647/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (43873562777/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (43873562777/250000000000:ℝ) ≤ taylorSin (882038953/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (6659697571/31250000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (134223319/625000000:ℝ) + taylorErr ≤ (6659697571/31250000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-984480457647/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-7816225123/8000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-6659697571/31250000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-43873562777/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3176874211711/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15922720578253/1000000000000:ℝ) := by nlinarith
  have hp1 : (26288611568339/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13176040161261/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-5615900330071/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2306750099927/500000000000:ℝ) := by nlinarith
  have hN : (3629019742207/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (126516515306561/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3629019742207/1000000000000:ℝ) (126516515306561/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (257119041/5000000000000:ℝ) ≤ ((3629019742207/1000000000000:ℝ)/(126516515306561/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1356 (x : ℝ) (h₁ : (20711/4096:ℝ) ≤ x) (h₂ : x ≤ (41533/8192:ℝ)) : (519328881/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (177174781/1000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2197427479/10000000000:ℝ) := by nlinarith
  have hc1 : (195190710961/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (195190710961/200000000000:ℝ) ≤ taylorCos (2197427479/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (12304319571/12500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (177174781/1000000000:ℝ) + taylorErr ≤ (12304319571/12500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (176249286473/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (176249286473/1000000000000:ℝ) ≤ taylorSin (177174781/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (27247320807/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2197427479/10000000000:ℝ) + taylorErr ≤ (27247320807/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-12304319571/12500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-195190710961/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-27247320807/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-176249286473/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15885138048949/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (7963853007907/500000000000:ℝ) := by nlinarith
  have hp1 : (26289880936353/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (6590082803681/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-5745987209491/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1158393189123/250000000000:ℝ) := by nlinarith
  have hN : (912306797703/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (101276727570479/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (912306797703/250000000000:ℝ) (101276727570479/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (519328881/10000000000000:ℝ) ≤ ((912306797703/250000000000:ℝ)/(101276727570479/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1357 (x : ℝ) (h₁ : (20711/4096:ℝ) ≤ x) (h₂ : x ≤ (10391/2048:ℝ)) : (32361139/625000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (177174781/1000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (231631099/1000000000:ℝ) := by nlinarith
  have hc1 : (486646621893/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (486646621893/500000000000:ℝ) ≤ taylorCos (231631099/1000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (12304319571/12500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (177174781/1000000000:ℝ) + taylorErr ≤ (12304319571/12500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (176249286473/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (176249286473/1000000000000:ℝ) ≤ taylorSin (177174781/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (229565368111/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (231631099/1000000000:ℝ) + taylorErr ≤ (229565368111/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-12304319571/12500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-486646621893/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-229565368111/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-176249286473/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15885138048949/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (398489859173/25000000000:ℝ) := by nlinarith
  have hp1 : (26289880936353/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (6595001604801/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1513983971099/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1158393189123/250000000000:ℝ) := by nlinarith
  have hN : (912306797703/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (63392667145487/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (912306797703/250000000000:ℝ) (63392667145487/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (32361139/625000000000:ℝ) ≤ ((912306797703/250000000000:ℝ)/(63392667145487/125000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1358 (x : ℝ) (h₁ : (2589/512:ℝ) ≤ x) (h₂ : x ≤ (41515/8192:ℝ)) : (26300467/500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1779417713/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (266049793/1250000000:ℝ) := by nlinarith
  have hc1 : (977434977923/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (977434977923/1000000000000:ℝ) ≤ taylorCos (266049793/1250000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (492105047333/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1779417713/10000000000:ℝ) + taylorErr ≤ (492105047333/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (177004218057/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (177004218057/1000000000000:ℝ) ≤ taylorSin (1779417713/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (13202281477/62500000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (266049793/1250000000:ℝ) + taylorErr ≤ (13202281477/62500000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-492105047333/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-977434977923/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-13202281477/62500000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-177004218057/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15885905039343/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15920803102269/1000000000000:ℝ) := by nlinarith
  have hp1 : (26291150304367/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13174453451223/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2782925484299/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-4653644501443/1000000000000:ℝ) := by nlinarith
  have hN : (3669434406777/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (505943942842437/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3669434406777/1000000000000:ℝ) (505943942842437/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (26300467/500000000000:ℝ) ≤ ((3669434406777/1000000000000:ℝ)/(505943942842437/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1359 (x : ℝ) (h₁ : (20713/4096:ℝ) ≤ x) (h₂ : x ≤ (41537/8192:ℝ)) : (66336319/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1787087617/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2212767287/10000000000:ℝ) := by nlinarith
  have hc1 : (975618031747/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (975618031747/1000000000000:ℝ) ≤ taylorCos (2212767287/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (984074044649/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1787087617/10000000000:ℝ) + taylorErr ≤ (984074044649/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (44439761403/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (44439761403/250000000000:ℝ) ≤ taylorSin (1787087617/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (8779016137/40000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2212767287/10000000000:ℝ) + taylorErr ≤ (8779016137/40000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-984074044649/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-975618031747/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-8779016137/40000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-44439761403/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15886672029737/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (7964619998301/500000000000:ℝ) := by nlinarith
  have hp1 : (26292419672381/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13181434975393/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-578600151789/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-292107214237/62500000000:ℝ) := by nlinarith
  have hN : (3689641383143/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (50648137373869/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3689641383143/1000000000000:ℝ) (50648137373869/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (66336319/1250000000000:ℝ) ≤ ((3689641383143/1000000000000:ℝ)/(50648137373869/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1360 (x : ℝ) (h₁ : (20713/4096:ℝ) ≤ x) (h₂ : x ≤ (1299/256:ℝ)) : (529106123/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1787087617/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1165825399/5000000000:ℝ) := by nlinarith
  have hc1 : (486469974967/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (486469974967/500000000000:ℝ) ≤ taylorCos (1165825399/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (984074044649/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1787087617/10000000000:ℝ) + taylorErr ≤ (984074044649/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (44439761403/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (44439761403/250000000000:ℝ) ≤ taylorSin (1787087617/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (231058110583/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1165825399/5000000000:ℝ) + taylorErr ≤ (231058110583/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-984074044649/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-486469974967/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-231058110583/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-44439761403/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15886672029737/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3985282086927/250000000000:ℝ) := by nlinarith
  have hp1 : (26292419672381/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13191272577633/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-6095901035947/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-292107214237/62500000000:ℝ) := by nlinarith
  have hN : (3689641383143/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (2536195729981/5000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3689641383143/1000000000000:ℝ) (2536195729981/5000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (529106123/10000000000000:ℝ) ≤ ((3689641383143/1000000000000:ℝ)/(2536195729981/5000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1361 (x : ℝ) (h₁ : (20713/4096:ℝ) ≤ x) (h₂ : x ≤ (2603/512:ℝ)) : (13126113/250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1787087617/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (659611739/2500000000:ℝ) := by nlinarith
  have hc1 : (482697219707/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (482697219707/500000000000:ℝ) ≤ taylorCos (659611739/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (984074044649/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1787087617/10000000000:ℝ) + taylorErr ≤ (984074044649/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (44439761403/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (44439761403/250000000000:ℝ) ≤ taylorSin (1787087617/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (130397060129/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (659611739/2500000000:ℝ) + taylorErr ≤ (130397060129/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-984074044649/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-482697219707/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-130397060129/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-44439761403/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15886672029737/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (7985903981733/500000000000:ℝ) := by nlinarith
  have hp1 : (26292419672381/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3304164984563/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1723413600673/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-292107214237/62500000000:ℝ) := by nlinarith
  have hN : (3689641383143/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (63649662405459/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3689641383143/1000000000000:ℝ) (63649662405459/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (13126113/250000000000:ℝ) ≤ ((3689641383143/1000000000000:ℝ)/(63649662405459/125000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1362 (x : ℝ) (h₁ : (41433/8192:ℝ) ≤ x) (h₂ : x ≤ (1297/256:ℝ)) : (110597717/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1813932281/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (130388367/625000000:ℝ) := by nlinarith
  have hc1 : (7643104441/7812500000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (7643104441/7812500000:ℝ) ≤ taylorCos (130388367/625000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (983593311237/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1813932281/10000000000:ℝ) + taylorErr ≤ (983593311237/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (180400115643/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (180400115643/1000000000000:ℝ) ≤ taylorSin (1813932281/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (207111378501/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (130388367/625000000:ℝ) + taylorErr ≤ (207111378501/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-983593311237/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-7643104441/7812500000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-207111378501/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-180400115643/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3972339124029/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (7958292327551/500000000000:ℝ) := by nlinarith
  have hp1 : (2629686246043/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1053677015131/40000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2727856238733/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-4743957028909/1000000000000:ℝ) := by nlinarith
  have hN : (470045464709/125000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (505675334166057/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (470045464709/125000000000:ℝ) (505675334166057/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (110597717/2000000000000:ℝ) ≤ ((470045464709/125000000000:ℝ)/(505675334166057/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1363 (x : ℝ) (h₁ : (41435/8192:ℝ) ≤ x) (h₂ : x ≤ (20763/4096:ℝ)) : (278880729/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (364320437/2000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (434116563/2000000000:ℝ) := by nlinarith
  have hc1 : (976535193699/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (976535193699/1000000000000:ℝ) ≤ taylorCos (434116563/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (49172732839/50000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (364320437/2000000000:ℝ) + taylorErr ≤ (49172732839/50000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (45288617283/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (45288617283/250000000000:ℝ) ≤ taylorSin (364320437/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (26919733707/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (434116563/2000000000:ℝ) + taylorErr ≤ (26919733707/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-49172732839/50000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-976535193699/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-26919733707/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-45288617283/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1589012348651/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3185004309887/200000000000:ℝ) := by nlinarith
  have hp1 : (6574532957111/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5271177685323/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-88686687257/15625000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-952804822109/200000000000:ℝ) := by nlinarith
  have hN : (756113890753/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (506212622699939/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (756113890753/200000000000:ℝ) (506212622699939/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (278880729/5000000000000:ℝ) ≤ ((756113890753/200000000000:ℝ)/(506212622699939/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1364 (x : ℝ) (h₁ : (1295/256:ℝ) ≤ x) (h₂ : x ≤ (2595/512:ℝ)) : (114619513/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (368155389/2000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (134223319/625000000:ℝ) := by nlinarith
  have hc1 : (7816225123/8000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (7816225123/8000000000:ℝ) ≤ taylorCos (134223319/625000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (491552744851/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (368155389/2000000000:ℝ) + taylorErr ≤ (491552744851/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (183039885647/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (183039885647/1000000000000:ℝ) ≤ taylorSin (368155389/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (6659697571/31250000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (134223319/625000000:ℝ) + taylorErr ≤ (6659697571/31250000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-491552744851/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-7816225123/8000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-6659697571/31250000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-183039885647/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3178408192499/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15922720578253/1000000000000:ℝ) := by nlinarith
  have hp1 : (26301305248479/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13176040161261/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-5615900330071/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-601773488131/125000000000:ℝ) := by nlinarith
  have hN : (1915541207673/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (126516515306561/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1915541207673/500000000000:ℝ) (126516515306561/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (114619513/2000000000000:ℝ) ≤ ((1915541207673/500000000000:ℝ)/(126516515306561/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1365 (x : ℝ) (h₁ : (1295/256:ℝ) ≤ x) (h₂ : x ≤ (10385/2048:ℝ)) : (571992483/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (368155389/2000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2224272143/10000000000:ℝ) := by nlinarith
  have hc1 : (487682441421/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (487682441421/500000000000:ℝ) ≤ taylorCos (2224272143/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (491552744851/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (368155389/2000000000:ℝ) + taylorErr ≤ (491552744851/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (183039885647/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (183039885647/1000000000000:ℝ) ≤ taylorSin (368155389/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (110298846213/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2224272143/10000000000:ℝ) + taylorErr ≤ (110298846213/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-491552744851/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-487682441421/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-110298846213/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-183039885647/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3178408192499/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15930390482193/1000000000000:ℝ) := by nlinarith
  have hp1 : (26301305248479/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26364774002833/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2908004153179/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-601773488131/125000000000:ℝ) := by nlinarith
  have hN : (1915541207673/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (506554681830291/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1915541207673/500000000000:ℝ) (506554681830291/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (571992483/10000000000000:ℝ) ≤ ((1915541207673/500000000000:ℝ)/(506554681830291/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1366 (x : ℝ) (h₁ : (1295/256:ℝ) ≤ x) (h₂ : x ≤ (5195/1024:ℝ)) : (114178013/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (368155389/2000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1150485591/5000000000:ℝ) := by nlinarith
  have hc1 : (194728849477/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (194728849477/200000000000:ℝ) ≤ taylorCos (1150485591/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (491552744851/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (368155389/2000000000:ℝ) + taylorErr ≤ (491552744851/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (183039885647/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (183039885647/1000000000000:ℝ) ≤ taylorSin (368155389/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (4561441709/20000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1150485591/5000000000:ℝ) + taylorErr ≤ (4561441709/20000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-491552744851/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-194728849477/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-4561441709/20000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-183039885647/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3178408192499/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3984515096533/250000000000:ℝ) := by nlinarith
  have hp1 : (26301305248479/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26377467683141/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-751995507923/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-601773488131/125000000000:ℝ) := by nlinarith
  have hN : (1915541207673/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (507043537743981/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1915541207673/500000000000:ℝ) (507043537743981/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (114178013/2000000000000:ℝ) ≤ ((1915541207673/500000000000:ℝ)/(507043537743981/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1367 (x : ℝ) (h₁ : (1295/256:ℝ) ≤ x) (h₂ : x ≤ (325/64:ℝ)) : (568693187/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (368155389/2000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2454369261/10000000000:ℝ) := by nlinarith
  have hc1 : (970031250923/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (970031250923/1000000000000:ℝ) ≤ taylorCos (2454369261/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (491552744851/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (368155389/2000000000:ℝ) + taylorErr ≤ (491552744851/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (183039885647/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (183039885647/1000000000000:ℝ) ≤ taylorSin (368155389/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (242980182203/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2454369261/10000000000:ℝ) + taylorErr ≤ (242980182203/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-491552744851/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-970031250923/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-242980182203/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-183039885647/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3178408192499/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15953400194011/1000000000000:ℝ) := by nlinarith
  have hp1 : (26301305248479/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26402855043761/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-6415370529213/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-601773488131/125000000000:ℝ) := by nlinarith
  have hN : (1915541207673/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (508021955500541/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1915541207673/500000000000:ℝ) (508021955500541/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (568693187/10000000000000:ℝ) ≤ ((1915541207673/500000000000:ℝ)/(508021955500541/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1368 (x : ℝ) (h₁ : (1295/256:ℝ) ≤ x) (h₂ : x ≤ (5205/1024:ℝ)) : (566506871/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (368155389/2000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (130388367/500000000:ℝ) := by nlinarith
  have hc1 : (60386875073/62500000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (60386875073/62500000000:ℝ) ≤ taylorCos (130388367/500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (491552744851/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (368155389/2000000000:ℝ) + taylorErr ≤ (491552744851/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (183039885647/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (183039885647/1000000000000:ℝ) ≤ taylorSin (368155389/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (128915552241/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (130388367/500000000:ℝ) + taylorErr ≤ (128915552241/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-491552744851/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-60386875073/62500000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-128915552241/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-183039885647/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3178408192499/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1596874000189/100000000000:ℝ) := by nlinarith
  have hp1 : (26301305248479/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1321412120219/50000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-5323455413/781250000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-601773488131/125000000000:ℝ) := by nlinarith
  have hN : (1915541207673/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (127250328623981/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1915541207673/500000000000:ℝ) (127250328623981/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (566506871/10000000000000:ℝ) ≤ ((1915541207673/500000000000:ℝ)/(127250328623981/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1369 (x : ℝ) (h₁ : (1295/256:ℝ) ≤ x) (h₂ : x ≤ (2605/512:ℝ)) : (112866211/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (368155389/2000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2761165419/10000000000:ℝ) := by nlinarith
  have hc1 : (192424280397/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (192424280397/200000000000:ℝ) ≤ taylorCos (2761165419/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (491552744851/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (368155389/2000000000:ℝ) + taylorErr ≤ (491552744851/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (183039885647/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (183039885647/1000000000000:ℝ) ≤ taylorSin (368155389/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (27262135779/100000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2761165419/10000000000:ℝ) + taylorErr ≤ (27262135779/100000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-491552744851/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-192424280397/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-27262135779/100000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-183039885647/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3178408192499/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15984079809769/1000000000000:ℝ) := by nlinarith
  have hp1 : (26301305248479/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26453629764999/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-450739029063/62500000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-601773488131/125000000000:ℝ) := by nlinarith
  have hN : (1915541207673/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (50998161473013/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1915541207673/500000000000:ℝ) (50998161473013/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (112866211/2000000000000:ℝ) ≤ ((1915541207673/500000000000:ℝ)/(50998161473013/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1370 (x : ℝ) (h₁ : (1295/256:ℝ) ≤ x) (h₂ : x ≤ (1305/256:ℝ)) : (560010683/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (368155389/2000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (383495197/1250000000:ℝ) := by nlinarith
  have hc1 : (190661207617/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (190661207617/200000000000:ℝ) ≤ taylorCos (383495197/1250000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (491552744851/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (368155389/2000000000:ℝ) + taylorErr ≤ (491552744851/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (183039885647/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (183039885647/1000000000000:ℝ) ≤ taylorSin (368155389/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (302005951603/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (383495197/1250000000:ℝ) + taylorErr ≤ (302005951603/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-491552744851/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-190661207617/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-302005951603/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-183039885647/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3178408192499/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (16014759425527/1000000000000:ℝ) := by nlinarith
  have hp1 : (26301305248479/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13252202243119/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-4002243949269/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-601773488131/125000000000:ℝ) := by nlinarith
  have hN : (1915541207673/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (127986259728753/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1915541207673/500000000000:ℝ) (127986259728753/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (560010683/10000000000000:ℝ) ≤ ((1915541207673/500000000000:ℝ)/(127986259728753/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1371 (x : ℝ) (h₁ : (1295/256:ℝ) ≤ x) (h₂ : x ≤ (2615/512:ℝ)) : (69466449/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (368155389/2000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1687378867/5000000000:ℝ) := by nlinarith
  have hc1 : (471796727939/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (471796727939/500000000000:ℝ) ≤ taylorCos (1687378867/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (491552744851/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (368155389/2000000000:ℝ) + taylorErr ≤ (491552744851/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (183039885647/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (183039885647/1000000000000:ℝ) ≤ taylorSin (368155389/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (82776577021/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1687378867/5000000000:ℝ) + taylorErr ≤ (82776577021/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-491552744851/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-471796727939/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-82776577021/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-183039885647/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3178408192499/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (4011359760321/250000000000:ℝ) := by nlinarith
  have hp1 : (26301305248479/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13277589603737/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1099073418487/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-601773488131/125000000000:ℝ) := by nlinarith
  have hN : (1915541207673/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (256956114027561/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1915541207673/500000000000:ℝ) (256956114027561/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (69466449/1250000000000:ℝ) ≤ ((1915541207673/500000000000:ℝ)/(256956114027561/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1372 (x : ℝ) (h₁ : (1295/256:ℝ) ≤ x) (h₂ : x ≤ (655/128:ℝ)) : (551493311/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (368155389/2000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (3681553891/10000000000:ℝ) := by nlinarith
  have hc1 : (93299279657/100000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (93299279657/100000000000:ℝ) ≤ taylorCos (3681553891/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (491552744851/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (368155389/2000000000:ℝ) + taylorErr ≤ (491552744851/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (183039885647/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (183039885647/1000000000000:ℝ) ≤ taylorSin (368155389/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (89973759701/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3681553891/10000000000:ℝ) + taylorErr ≤ (89973759701/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-491552744851/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-93299279657/100000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-89973759701/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-183039885647/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3178408192499/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (8038059328521/500000000000:ℝ) := by nlinarith
  have hp1 : (26301305248479/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26605953928713/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1196918852699/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-601773488131/125000000000:ℝ) := by nlinarith
  have hN : (1915541207673/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (128970795537647/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1915541207673/500000000000:ℝ) (128970795537647/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (551493311/10000000000000:ℝ) ≤ ((1915541207673/500000000000:ℝ)/(128970795537647/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1373 (x : ℝ) (h₁ : (1295/256:ℝ) ≤ x) (h₂ : x ≤ (1315/256:ℝ)) : (108627463/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (368155389/2000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (4295146207/10000000000:ℝ) := by nlinarith
  have hc1 : (90916798079/100000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (90916798079/100000000000:ℝ) ≤ taylorCos (4295146207/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (491552744851/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (368155389/2000000000:ℝ) + taylorErr ≤ (491552744851/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (183039885647/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (183039885647/1000000000000:ℝ) ≤ taylorSin (368155389/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (416429562443/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (4295146207/10000000000:ℝ) + taylorErr ≤ (416429562443/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-491552744851/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-90916798079/100000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-416429562443/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-183039885647/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3178408192499/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (16137477888557/1000000000000:ℝ) := by nlinarith
  have hp1 : (26301305248479/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (6676875842797/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-11121793942809/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-601773488131/125000000000:ℝ) := by nlinarith
  have hN : (1915541207673/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (519836385207333/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1915541207673/500000000000:ℝ) (519836385207333/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (108627463/2000000000000:ℝ) ≤ ((1915541207673/500000000000:ℝ)/(519836385207333/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1374 (x : ℝ) (h₁ : (1295/256:ℝ) ≤ x) (h₂ : x ≤ (165/32:ℝ)) : (534939039/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (368155389/2000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2454369261/5000000000:ℝ) := by nlinarith
  have hc1 : (17638425241/20000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (17638425241/20000000000:ℝ) ≤ taylorCos (2454369261/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (491552744851/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (368155389/2000000000:ℝ) + taylorErr ≤ (491552744851/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (183039885647/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (183039885647/1000000000000:ℝ) ≤ taylorSin (368155389/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (117849184789/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2454369261/5000000000:ℝ) + taylorErr ≤ (117849184789/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-491552744851/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-17638425241/20000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-117849184789/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-183039885647/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3178408192499/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (16198837120073/1000000000000:ℝ) := by nlinarith
  have hp1 : (26301305248479/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5361810562733/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-12637700076223/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-601773488131/125000000000:ℝ) := by nlinarith
  have hN : (1915541207673/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (52380464808531/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1915541207673/500000000000:ℝ) (52380464808531/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (534939039/10000000000000:ℝ) ≤ ((1915541207673/500000000000:ℝ)/(52380464808531/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1375 (x : ℝ) (h₁ : (10361/2048:ℝ) ≤ x) (h₂ : x ≤ (41515/8192:ℝ)) : (23421341/400000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1856116753/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (266049793/1250000000:ℝ) := by nlinarith
  have hc1 : (977434977923/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (977434977923/1000000000000:ℝ) ≤ taylorCos (266049793/1250000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (982823553467/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1856116753/10000000000:ℝ) + taylorErr ≤ (982823553467/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (184547734643/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (184547734643/1000000000000:ℝ) ≤ taylorSin (1856116753/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (13202281477/62500000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (266049793/1250000000:ℝ) + taylorErr ≤ (13202281477/62500000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-982823553467/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-977434977923/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-13202281477/62500000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-184547734643/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15893574943283/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15920803102269/1000000000000:ℝ) := by nlinarith
  have hp1 : (26303843984507/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (13174453451223/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2782925484299/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-4854314819743/1000000000000:ℝ) := by nlinarith
  have hN : (967872816569/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (505943942842437/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (967872816569/250000000000:ℝ) (505943942842437/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (23421341/400000000000:ℝ) ≤ ((967872816569/250000000000:ℝ)/(505943942842437/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1376 (x : ℝ) (h₁ : (10361/2048:ℝ) ≤ x) (h₂ : x ≤ (41555/8192:ℝ)) : (11665557/200000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1856116753/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (1140898211/5000000000:ℝ) := by nlinarith
  have hc1 : (974079779957/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (974079779957/1000000000000:ℝ) ≤ taylorCos (1140898211/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (982823553467/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1856116753/10000000000:ℝ) + taylorErr ≤ (982823553467/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (184547734643/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (184547734643/1000000000000:ℝ) ≤ taylorSin (1856116753/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (45240945567/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1140898211/5000000000:ℝ) + taylorErr ≤ (45240945567/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-982823553467/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-974079779957/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-45240945567/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-184547734643/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15893574943283/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15936142910147/1000000000000:ℝ) := by nlinarith
  have hp1 : (26303843984507/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3296786782883/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-5965990055617/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-4854314819743/1000000000000:ℝ) := by nlinarith
  have hN : (967872816569/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (506921301705257/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (967872816569/250000000000:ℝ) (506921301705257/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (11665557/200000000000:ℝ) ≤ ((967872816569/250000000000:ℝ)/(506921301705257/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1377 (x : ℝ) (h₁ : (10361/2048:ℝ) ≤ x) (h₂ : x ≤ (163/32:ℝ)) : (57364627/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1856116753/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2945243113/10000000000:ℝ) := by nlinarith
  have hc1 : (956940333463/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (956940333463/1000000000000:ℝ) ≤ taylorCos (2945243113/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (982823553467/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1856116753/10000000000:ℝ) + taylorErr ≤ (982823553467/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (184547734643/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (184547734643/1000000000000:ℝ) ≤ taylorSin (1856116753/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (290284679541/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2945243113/10000000000:ℝ) + taylorErr ≤ (290284679541/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-982823553467/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-956940333463/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-290284679541/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-184547734643/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15893574943283/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2000310947403/125000000000:ℝ) := by nlinarith
  have hp1 : (26303843984507/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26484094597743/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-192198172831/25000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-4854314819743/1000000000000:ℝ) := by nlinarith
  have hN : (967872816569/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (511159217446437/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (967872816569/250000000000:ℝ) (511159217446437/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (57364627/1000000000000:ℝ) ≤ ((967872816569/250000000000:ℝ)/(511159217446437/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1378 (x : ℝ) (h₁ : (10361/2048:ℝ) ≤ x) (h₂ : x ≤ (2613/512:ℝ)) : (569259631/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1856116753/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (3252039271/10000000000:ℝ) := by nlinarith
  have hc1 : (473792794367/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (473792794367/500000000000:ℝ) ≤ taylorCos (3252039271/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (982823553467/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1856116753/10000000000:ℝ) + taylorErr ≤ (982823553467/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (184547734643/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (184547734643/1000000000000:ℝ) ≤ taylorSin (1856116753/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (319502033143/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3252039271/10000000000:ℝ) + taylorErr ≤ (319502033143/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-982823553467/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-473792794367/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-319502033143/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-184547734643/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15893574943283/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (16033167194981/1000000000000:ℝ) := by nlinarith
  have hp1 : (26303843984507/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (26534869318979/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-4238972348299/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-4854314819743/1000000000000:ℝ) := by nlinarith
  have hN : (967872816569/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (51312490060443/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (967872816569/250000000000:ℝ) (51312490060443/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (569259631/10000000000000:ℝ) ≤ ((967872816569/250000000000:ℝ)/(51312490060443/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_1379 (x : ℝ) (h₁ : (5181/1024:ℝ) ≤ x) (h₂ : x ≤ (20795/4096:ℝ)) : (593510889/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1871456561/10000000000:ℝ) ≤ Real.pi * (x - (5:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (5:ℝ)) ≤ (2416019741/10000000000:ℝ) := by nlinarith
  have hc1 : (970955932919/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (970955932919/1000000000000:ℝ) ≤ taylorCos (2416019741/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (5:ℝ))) ≤ (491269652277/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1871456561/10000000000:ℝ) + taylorErr ≤ (491269652277/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (9302757469/50000000000:ℝ) ≤ Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (9302757469/50000000000:ℝ) ≤ taylorSin (1871456561/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (5:ℝ))) ≤ (239258381291/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2416019741/10000000000:ℝ) + taylorErr ≤ (239258381291/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).1
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (5:ℝ))) := by
    have h := (trig_shift (5:ℝ) (x - (5:ℝ))).2
    rw [show (5:ℝ) + (x - (5:ℝ)) = x by ring, cs_5.1, cs_5.2] at h
    rw [h]; ring
  have hcxl : (-491269652277/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-970955932919/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-239258381291/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-9302757469/50000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (15895108924071/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (15949565242041/1000000000000:ℝ) := by nlinarith
  have hp1 : (5261276544107/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5279301640721/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-631558582453/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1223609491679/250000000000:ℝ) := by nlinarith
  have hN : (1955949331081/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (101555452564049/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1955949331081/500000000000:ℝ) (101555452564049/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (593510889/10000000000000:ℝ) ≤ ((1955949331081/500000000000:ℝ)/(101555452564049/200000000000:ℝ))^2 := by norm_num
  linarith

end Zeta23Ext.Bridge.FourPoint
