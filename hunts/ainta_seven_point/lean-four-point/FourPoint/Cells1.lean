import FourPoint.Base

noncomputable section
open Real
namespace Zeta23Ext.Bridge.FourPoint


theorem wc_60 (x : ℝ) (h₁ : (17143/16384:ℝ) ≤ x) (h₂ : x ≤ (4287/4096:ℝ)) : (446763507/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (90960267/625000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1464951653/10000000000:ℝ) := by nlinarith
  have hc1 : (494644378797/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (494644378797/500000000000:ℝ) ≤ taylorCos (1464951653/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (494714128051/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (90960267/625000000:ℝ) + taylorErr ≤ (494714128051/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (36255801129/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (36255801129/250000000000:ℝ) ≤ taylorSin (90960267/625000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (18246468101/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1464951653/10000000000:ℝ) + taylorErr ≤ (18246468101/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-494714128051/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-494644378797/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-18246468101/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-36255801129/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (82178227021/25000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3288087818833/1000000000000:ℝ) := by nlinarith
  have hp1 : (1360048491417/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5441780748683/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-198586557687/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-788954362089/1000000000000:ℝ) := by nlinarith
  have hN : (97471263423/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (5155760752179/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (97471263423/500000000000:ℝ) (5155760752179/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (446763507/5000000000000:ℝ) ≤ ((97471263423/500000000000:ℝ)/(5155760752179/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_61 (x : ℝ) (h₁ : (4287/4096:ℝ) ≤ x) (h₂ : x ≤ (17153/16384:ℝ)) : (168496229/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (366237913/2500000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1474539033/10000000000:ℝ) := by nlinarith
  have hc1 : (989148354293/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (989148354293/1000000000000:ℝ) ≤ taylorCos (1474539033/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (989288762133/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (366237913/2500000000:ℝ) + taylorErr ≤ (989288762133/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (29194348037/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (29194348037/200000000000:ℝ) ≤ taylorSin (366237913/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (146920146303/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1474539033/10000000000:ℝ) + taylorErr ≤ (146920146303/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-989288762133/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-989148354293/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-146920146303/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-29194348037/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (205505488677/62500000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1644523278413/500000000000:ℝ) := by nlinarith
  have hp1 : (1088356135137/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5443367458723/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-799740343417/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-397173097467/500000000000:ℝ) := by nlinarith
  have hN : (47352002719/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10317827252969/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (47352002719/250000000000:ℝ) (10317827252969/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (168496229/2000000000000:ℝ) ≤ ((47352002719/250000000000:ℝ)/(10317827252969/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_62 (x : ℝ) (h₁ : (4287/4096:ℝ) ≤ x) (h₂ : x ≤ (8579/8192:ℝ)) : (396484213/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (366237913/2500000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1484126413/10000000000:ℝ) := by nlinarith
  have hc1 : (989007041787/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (989007041787/1000000000000:ℝ) ≤ taylorCos (1484126413/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (989288762133/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (366237913/2500000000:ℝ) + taylorErr ≤ (989288762133/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (29194348037/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (29194348037/200000000000:ℝ) ≤ taylorSin (366237913/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (9241775797/62500000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1484126413/10000000000:ℝ) + taylorErr ≤ (9241775797/62500000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-989288762133/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-989007041787/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-9241775797/62500000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-29194348037/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (205505488677/62500000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1645002647409/500000000000:ℝ) := by nlinarith
  have hp1 : (1088356135137/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5444954168761/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-805136730443/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-397173097467/500000000000:ℝ) := by nlinarith
  have hN : (11491894459/62500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20648269679861/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (11491894459/62500000000:ℝ) (20648269679861/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (396484213/5000000000000:ℝ) ≤ ((11491894459/62500000000:ℝ)/(20648269679861/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_63 (x : ℝ) (h₁ : (4287/4096:ℝ) ≤ x) (h₂ : x ≤ (1073/1024:ℝ)) : (349265369/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (366237913/2500000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1503301173/10000000000:ℝ) := by nlinarith
  have hc1 : (197744337937/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (197744337937/200000000000:ℝ) ≤ taylorCos (1503301173/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (989288762133/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (366237913/2500000000:ℝ) + taylorErr ≤ (989288762133/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (29194348037/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (29194348037/200000000000:ℝ) ≤ taylorSin (366237913/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (74882268513/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1503301173/10000000000:ℝ) + taylorErr ≤ (74882268513/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-989288762133/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-197744337937/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-74882268513/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-29194348037/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (205505488677/62500000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3291922770803/1000000000000:ℝ) := by nlinarith
  have hp1 : (1088356135137/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5448127588839/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-407968153001/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-397173097467/500000000000:ℝ) := by nlinarith
  have hN : (172785383683/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20673511057863/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (172785383683/1000000000000:ℝ) (20673511057863/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (349265369/5000000000000:ℝ) ≤ ((172785383683/1000000000000:ℝ)/(20673511057863/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_64 (x : ℝ) (h₁ : (17153/16384:ℝ) ≤ x) (h₂ : x ≤ (8579/8192:ℝ)) : (396484213/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (184317379/1250000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1484126413/10000000000:ℝ) := by nlinarith
  have hc1 : (989007041787/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (989007041787/1000000000000:ℝ) ≤ taylorCos (1484126413/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (61821772427/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (184317379/1250000000:ℝ) + taylorErr ≤ (61821772427/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (1836501771/12500000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (1836501771/12500000000:ℝ) ≤ taylorSin (184317379/1250000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (9241775797/62500000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1484126413/10000000000:ℝ) + taylorErr ≤ (9241775797/62500000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-61821772427/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-989007041787/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-9241775797/62500000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-1836501771/12500000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (131561862273/40000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1645002647409/500000000000:ℝ) := by nlinarith
  have hp1 : (5443367385703/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5444954168761/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-805136730443/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-799740307523/1000000000000:ℝ) := by nlinarith
  have hN : (11491894459/62500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20648269679861/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (11491894459/62500000000:ℝ) (20648269679861/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (396484213/5000000000000:ℝ) ≤ ((11491894459/62500000000:ℝ)/(20648269679861/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_65 (x : ℝ) (h₁ : (8579/8192:ℝ) ≤ x) (h₂ : x ≤ (17163/16384:ℝ)) : (186246483/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (371031603/2500000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1493713793/10000000000:ℝ) := by nlinarith
  have hc1 : (61804051263/62500000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (61804051263/62500000000:ℝ) ≤ taylorCos (1493713793/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (494503523163/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (371031603/2500000000:ℝ) + taylorErr ≤ (494503523163/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (147868408129/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (147868408129/1000000000000:ℝ) ≤ taylorSin (371031603/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (148816543283/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1493713793/10000000000:ℝ) + taylorErr ≤ (148816543283/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-494503523163/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-61804051263/62500000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-148816543283/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-147868408129/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3290005294817/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3290964032811/1000000000000:ℝ) := by nlinarith
  have hp1 : (136123852393/25000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5446540878801/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-810535386433/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-805136694469/1000000000000:ℝ) := by nlinarith
  have hN : (7133177351/40000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (1291305533157/62500000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (7133177351/40000000000:ℝ) (1291305533157/62500000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (186246483/2500000000000:ℝ) ≤ ((7133177351/40000000000:ℝ)/(1291305533157/62500000000:ℝ))^2 := by norm_num
  linarith

theorem wc_66 (x : ℝ) (h₁ : (8579/8192:ℝ) ≤ x) (h₂ : x ≤ (1073/1024:ℝ)) : (349265369/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (371031603/2500000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1503301173/10000000000:ℝ) := by nlinarith
  have hc1 : (197744337937/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (197744337937/200000000000:ℝ) ≤ taylorCos (1503301173/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (494503523163/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (371031603/2500000000:ℝ) + taylorErr ≤ (494503523163/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (147868408129/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (147868408129/1000000000000:ℝ) ≤ taylorSin (371031603/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (74882268513/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1503301173/10000000000:ℝ) + taylorErr ≤ (74882268513/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-494503523163/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-197744337937/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-74882268513/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-147868408129/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3290005294817/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3291922770803/1000000000000:ℝ) := by nlinarith
  have hp1 : (136123852393/25000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5448127588839/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-407968153001/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-805136694469/1000000000000:ℝ) := by nlinarith
  have hN : (172785383683/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20673511057863/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (172785383683/1000000000000:ℝ) (20673511057863/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (349265369/5000000000000:ℝ) ≤ ((172785383683/1000000000000:ℝ)/(20673511057863/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_67 (x : ℝ) (h₁ : (17163/16384:ℝ) ≤ x) (h₂ : x ≤ (1073/1024:ℝ)) : (349265369/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (11669639/78125000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1503301173/10000000000:ℝ) := by nlinarith
  have hc1 : (197744337937/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (197744337937/200000000000:ℝ) ≤ taylorCos (1503301173/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (988864824747/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (11669639/78125000:ℝ) + taylorErr ≤ (988864824747/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (7440826933/50000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (7440826933/50000000000:ℝ) ≤ taylorSin (11669639/78125000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (74882268513/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1503301173/10000000000:ℝ) + taylorErr ≤ (74882268513/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-988864824747/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-197744337937/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-74882268513/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-7440826933/50000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (329096403281/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3291922770803/1000000000000:ℝ) := by nlinarith
  have hp1 : (2723270402869/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5448127588839/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-407968153001/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-40526767519/50000000000:ℝ) := by nlinarith
  have hN : (172785383683/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20673511057863/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (172785383683/1000000000000:ℝ) (20673511057863/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (349265369/5000000000000:ℝ) ≤ ((172785383683/1000000000000:ℝ)/(20673511057863/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_68 (x : ℝ) (h₁ : (1073/1024:ℝ) ≤ x) (h₂ : x ≤ (17173/16384:ℝ)) : (653599921/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (375825293/2500000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1512888553/10000000000:ℝ) := by nlinarith
  have hc1 : (988577650351/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (988577650351/1000000000000:ℝ) ≤ taylorCos (1512888553/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (61795105889/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (375825293/2500000000:ℝ) + taylorErr ≤ (61795105889/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (149764532403/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (149764532403/1000000000000:ℝ) ≤ taylorSin (375825293/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (37678098277/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1512888553/10000000000:ℝ) + taylorErr ≤ (37678098277/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-61795105889/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-988577650351/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-37678098277/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-149764532403/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1645961385401/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (823220377199/250000000000:ℝ) := by nlinarith
  have hp1 : (1089625503151/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2724857149439/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-821339483739/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-203984067467/250000000000:ℝ) := by nlinarith
  have hN : (41809541653/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10343068630971/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (41809541653/250000000000:ℝ) (10343068630971/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (653599921/10000000000000:ℝ) ≤ ((41809541653/250000000000:ℝ)/(10343068630971/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_69 (x : ℝ) (h₁ : (1073/1024:ℝ) ≤ x) (h₂ : x ≤ (8589/8192:ℝ)) : (3813691/62500000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (375825293/2500000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (380618983/2500000000:ℝ) := by nlinarith
  have hc1 : (61777043897/62500000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (61777043897/62500000000:ℝ) ≤ taylorCos (380618983/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (61795105889/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (375825293/2500000000:ℝ) + taylorErr ≤ (61795105889/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (149764532403/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (149764532403/1000000000000:ℝ) ≤ taylorSin (375825293/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (151660110559/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (380618983/2500000000:ℝ) + taylorErr ≤ (151660110559/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-61795105889/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-61777043897/62500000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-151660110559/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-149764532403/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1645961385401/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (823460061697/250000000000:ℝ) := by nlinarith
  have hp1 : (1089625503151/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1362825252229/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-826744913703/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-203984067467/250000000000:ℝ) := by nlinarith
  have hN : (161687788649/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20698767142721/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (161687788649/1000000000000:ℝ) (20698767142721/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (3813691/62500000000:ℝ) ≤ ((161687788649/1000000000000:ℝ)/(20698767142721/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_70 (x : ℝ) (h₁ : (1073/1024:ℝ) ≤ x) (h₂ : x ≤ (4297/4096:ℝ)) : (65990561/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (375825293/2500000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (385412673/2500000000:ℝ) := by nlinarith
  have hc1 : (988140080821/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (988140080821/1000000000000:ℝ) ≤ taylorCos (385412673/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (61795105889/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (375825293/2500000000:ℝ) + taylorErr ≤ (61795105889/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (149764532403/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (149764532403/1000000000000:ℝ) ≤ taylorSin (375825293/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (153555126581/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (385412673/2500000000:ℝ) + taylorErr ≤ (153555126581/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-61795105889/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-988140080821/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-153555126581/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-149764532403/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1645961385401/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3295757722773/1000000000000:ℝ) := by nlinarith
  have hp1 : (1089625503151/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2727237214497/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-418781255689/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-203984067467/250000000000:ℝ) := by nlinarith
  have hN : (150577569443/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (5181009483609/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (150577569443/1000000000000:ℝ) (5181009483609/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (65990561/1250000000000:ℝ) ≤ ((150577569443/1000000000000:ℝ)/(5181009483609/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_71 (x : ℝ) (h₁ : (1073/1024:ℝ) ≤ x) (h₂ : x ≤ (2151/2048:ℝ)) : (76304221/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (375825293/2500000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (395000053/2500000000:ℝ) := by nlinarith
  have hc1 : (39501757581/40000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (39501757581/40000000000:ℝ) ≤ taylorCos (395000053/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (61795105889/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (375825293/2500000000:ℝ) + taylorErr ≤ (61795105889/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (149764532403/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (149764532403/1000000000000:ℝ) ≤ taylorSin (375825293/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (78671728963/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (395000053/2500000000:ℝ) + taylorErr ≤ (78671728963/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-61795105889/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-39501757581/40000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-78671728963/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-149764532403/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1645961385401/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3299592674743/1000000000000:ℝ) := by nlinarith
  have hp1 : (1089625503151/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5460821269149/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-214806125401/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-203984067467/250000000000:ℝ) := by nlinarith
  have hN : (128319437921/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (5193655909609/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (128319437921/1000000000000:ℝ) (5193655909609/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (76304221/2000000000000:ℝ) ≤ ((128319437921/1000000000000:ℝ)/(5193655909609/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_72 (x : ℝ) (h₁ : (1073/1024:ℝ) ≤ x) (h₂ : x ≤ (539/512:ℝ)) : (160574441/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (375825293/2500000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1656699251/10000000000:ℝ) := by nlinarith
  have hc1 : (986308094981/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (986308094981/1000000000000:ℝ) ≤ taylorCos (1656699251/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (61795105889/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (375825293/2500000000:ℝ) + taylorErr ≤ (61795105889/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (149764532403/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (149764532403/1000000000000:ℝ) ≤ taylorSin (375825293/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (4122828069/25000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1656699251/10000000000:ℝ) + taylorErr ≤ (4122828069/25000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-61795105889/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-986308094981/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-4122828069/25000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-149764532403/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1645961385401/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1653631289341/500000000000:ℝ) := by nlinarith
  have hp1 : (1089625503151/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2736757474729/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-902654442789/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-203984067467/250000000000:ℝ) := by nlinarith
  have hN : (2614176631/31250000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20875971528701/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2614176631/31250000000:ℝ) (20875971528701/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (160574441/10000000000000:ℝ) ≤ ((2614176631/31250000000:ℝ)/(20875971528701/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_73 (x : ℝ) (h₁ : (17173/16384:ℝ) ≤ x) (h₂ : x ≤ (8589/8192:ℝ)) : (3813691/62500000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (189111069/1250000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (380618983/2500000000:ℝ) := by nlinarith
  have hc1 : (61777043897/62500000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (61777043897/62500000000:ℝ) ≤ taylorCos (380618983/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (98857765489/100000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (189111069/1250000000:ℝ) + taylorErr ≤ (98857765489/100000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (30142477697/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (30142477697/200000000000:ℝ) ≤ taylorSin (189111069/1250000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (151660110559/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (380618983/2500000000:ℝ) + taylorErr ≤ (151660110559/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-98857765489/100000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-61777043897/62500000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-151660110559/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-30142477697/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (658576301759/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (823460061697/250000000000:ℝ) := by nlinarith
  have hp1 : (2724857112887/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1362825252229/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-826744913703/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-821339447527/1000000000000:ℝ) := by nlinarith
  have hN : (161687788649/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20698767142721/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (161687788649/1000000000000:ℝ) (20698767142721/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (3813691/62500000000:ℝ) ≤ ((161687788649/1000000000000:ℝ)/(20698767142721/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_74 (x : ℝ) (h₁ : (8589/8192:ℝ) ≤ x) (h₂ : x ≤ (17183/16384:ℝ)) : (568299723/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1522475931/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (95753957/625000000:ℝ) := by nlinarith
  have hc1 : (988286845793/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (988286845793/1000000000000:ℝ) ≤ taylorCos (95753957/625000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (247108176723/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1522475931/10000000000:ℝ) + taylorErr ≤ (247108176723/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (9478756621/62500000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (9478756621/62500000000:ℝ) ≤ taylorSin (1522475931/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (152607688707/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (95753957/625000000:ℝ) + taylorErr ≤ (152607688707/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-247108176723/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-988286845793/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-152607688707/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-9478756621/62500000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3293840246787/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (164739949239/50000000000:ℝ) := by nlinarith
  have hp1 : (545130093579/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2726443859477/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-832152591569/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-82674487741/100000000000:ℝ) := by nlinarith
  have hN : (9758390889/62500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (4142280140043/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (9758390889/62500000000:ℝ) (4142280140043/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (568299723/10000000000000:ℝ) ≤ ((9758390889/62500000000:ℝ)/(4142280140043/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_75 (x : ℝ) (h₁ : (8589/8192:ℝ) ≤ x) (h₂ : x ≤ (4297/4096:ℝ)) : (65990561/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1522475931/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (385412673/2500000000:ℝ) := by nlinarith
  have hc1 : (988140080821/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (988140080821/1000000000000:ℝ) ≤ taylorCos (385412673/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (247108176723/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1522475931/10000000000:ℝ) + taylorErr ≤ (247108176723/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (9478756621/62500000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (9478756621/62500000000:ℝ) ≤ taylorSin (1522475931/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (153555126581/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (385412673/2500000000:ℝ) + taylorErr ≤ (153555126581/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-247108176723/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-988140080821/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-153555126581/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-9478756621/62500000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3293840246787/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3295757722773/1000000000000:ℝ) := by nlinarith
  have hp1 : (545130093579/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2727237214497/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-418781255689/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-82674487741/100000000000:ℝ) := by nlinarith
  have hN : (150577569443/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (5181009483609/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (150577569443/1000000000000:ℝ) (5181009483609/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (65990561/1250000000000:ℝ) ≤ ((150577569443/1000000000000:ℝ)/(5181009483609/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_76 (x : ℝ) (h₁ : (17183/16384:ℝ) ≤ x) (h₂ : x ≤ (4297/4096:ℝ)) : (65990561/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1532063311/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (385412673/2500000000:ℝ) := by nlinarith
  have hc1 : (988140080821/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (988140080821/1000000000000:ℝ) ≤ taylorCos (385412673/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (247071712583/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1532063311/10000000000:ℝ) + taylorErr ≤ (247071712583/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (38151921021/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (38151921021/250000000000:ℝ) ≤ taylorSin (1532063311/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (153555126581/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (385412673/2500000000:ℝ) + taylorErr ≤ (153555126581/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-247071712583/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-988140080821/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-153555126581/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-38151921021/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3294798984779/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3295757722773/1000000000000:ℝ) := by nlinarith
  have hp1 : (5452887645807/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2727237214497/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-418781255689/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-208038138799/250000000000:ℝ) := by nlinarith
  have hN : (150577569443/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (5181009483609/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (150577569443/1000000000000:ℝ) (5181009483609/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (65990561/1250000000000:ℝ) ≤ ((150577569443/1000000000000:ℝ)/(5181009483609/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_77 (x : ℝ) (h₁ : (4297/4096:ℝ) ≤ x) (h₂ : x ≤ (17193/16384:ℝ)) : (244530967/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1541650691/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (193904759/1250000000:ℝ) := by nlinarith
  have hc1 : (246998101893/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (246998101893/250000000000:ℝ) ≤ taylorCos (193904759/1250000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (988140085361/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1541650691/10000000000:ℝ) + taylorErr ≤ (988140085361/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (76777560979/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (76777560979/500000000000:ℝ) ≤ taylorSin (1541650691/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (154502423311/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (193904759/1250000000:ℝ) + taylorErr ≤ (154502423311/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-988140085361/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-246998101893/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-154502423311/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-76777560979/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (823939430693/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (659343292153/200000000000:ℝ) := by nlinarith
  have hp1 : (218178974233/40000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (682007642379/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-421487333857/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-33502498997/40000000000:ℝ) := by nlinarith
  have hN : (72508869929/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10368339422679/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (72508869929/500000000000:ℝ) (10368339422679/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (244530967/5000000000000:ℝ) ≤ ((72508869929/500000000000:ℝ)/(10368339422679/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_78 (x : ℝ) (h₁ : (4297/4096:ℝ) ≤ x) (h₂ : x ≤ (8599/8192:ℝ)) : (225854567/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1541650691/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (390206363/2500000000:ℝ) := by nlinarith
  have hc1 : (493921913091/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (493921913091/500000000000:ℝ) ≤ taylorCos (390206363/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (988140085361/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1541650691/10000000000:ℝ) + taylorErr ≤ (988140085361/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (76777560979/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (76777560979/500000000000:ℝ) ≤ taylorSin (1541650691/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (6217983121/40000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (390206363/2500000000:ℝ) + taylorErr ≤ (6217983121/40000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-988140085361/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-493921913091/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-6217983121/40000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-76777560979/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (823939430693/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1648837599379/500000000000:ℝ) := by nlinarith
  have hp1 : (218178974233/40000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5457647849071/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-212097263787/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-33502498997/40000000000:ℝ) := by nlinarith
  have hN : (69727385517/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (1296832714563/62500000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (69727385517/500000000000:ℝ) (1296832714563/62500000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (225854567/5000000000000:ℝ) ≤ ((69727385517/500000000000:ℝ)/(1296832714563/62500000000:ℝ))^2 := by norm_num
  linarith

theorem wc_79 (x : ℝ) (h₁ : (4297/4096:ℝ) ≤ x) (h₂ : x ≤ (2151/2048:ℝ)) : (76304221/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1541650691/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (395000053/2500000000:ℝ) := by nlinarith
  have hc1 : (39501757581/40000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (39501757581/40000000000:ℝ) ≤ taylorCos (395000053/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (988140085361/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1541650691/10000000000:ℝ) + taylorErr ≤ (988140085361/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (76777560979/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (76777560979/500000000000:ℝ) ≤ taylorSin (1541650691/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (78671728963/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (395000053/2500000000:ℝ) + taylorErr ≤ (78671728963/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-988140085361/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-39501757581/40000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-78671728963/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-76777560979/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (823939430693/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3299592674743/1000000000000:ℝ) := by nlinarith
  have hp1 : (218178974233/40000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5460821269149/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-214806125401/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-33502498997/40000000000:ℝ) := by nlinarith
  have hN : (128319437921/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (5193655909609/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (128319437921/1000000000000:ℝ) (5193655909609/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (76304221/2000000000000:ℝ) ≤ ((128319437921/1000000000000:ℝ)/(5193655909609/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_80 (x : ℝ) (h₁ : (17193/16384:ℝ) ≤ x) (h₂ : x ≤ (8599/8192:ℝ)) : (225854567/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1551238071/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (390206363/2500000000:ℝ) := by nlinarith
  have hc1 : (493921913091/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (493921913091/500000000000:ℝ) ≤ taylorCos (390206363/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (61749525757/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1551238071/10000000000:ℝ) + taylorErr ≤ (61749525757/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (603525073/3906250000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (603525073/3906250000:ℝ) ≤ taylorSin (1551238071/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (6217983121/40000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (390206363/2500000000:ℝ) + taylorErr ≤ (6217983121/40000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-61749525757/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-493921913091/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-6217983121/40000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-603525073/3906250000:ℝ) := by rw [hsx]; linarith
  have hb1 : (824179115191/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1648837599379/500000000000:ℝ) := by nlinarith
  have hp1 : (2728030532921/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5457647849071/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-212097263787/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-421487315591/500000000000:ℝ) := by nlinarith
  have hN : (69727385517/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (1296832714563/62500000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (69727385517/500000000000:ℝ) (1296832714563/62500000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (225854567/5000000000000:ℝ) ≤ ((69727385517/500000000000:ℝ)/(1296832714563/62500000000:ℝ))^2 := by norm_num
  linarith

theorem wc_81 (x : ℝ) (h₁ : (8599/8192:ℝ) ≤ x) (h₂ : x ≤ (17203/16384:ℝ)) : (207931583/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1560825451/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (49075401/312500000:ℝ) := by nlinarith
  have hc1 : (987694336787/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (987694336787/1000000000000:ℝ) ≤ taylorCos (49075401/312500000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (493921915361/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1560825451/10000000000:ℝ) + taylorErr ≤ (493921915361/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (77724786701/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (77724786701/500000000000:ℝ) ≤ taylorSin (1560825451/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (78198294927/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (49075401/312500000:ℝ) + taylorErr ≤ (78198294927/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-493921915361/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-987694336787/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-78198294927/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-77724786701/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3297675198757/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (13194535747/4000000000:ℝ) := by nlinarith
  have hp1 : (272882388793/50000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5459234559109/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-426902834129/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-169677803707/200000000000:ℝ) := by nlinarith
  have hN : (133888668529/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10380985848679/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (133888668529/1000000000000:ℝ) (10380985848679/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (207931583/5000000000000:ℝ) ≤ ((133888668529/1000000000000:ℝ)/(10380985848679/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_82 (x : ℝ) (h₁ : (8599/8192:ℝ) ≤ x) (h₂ : x ≤ (2151/2048:ℝ)) : (76304221/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1560825451/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (395000053/2500000000:ℝ) := by nlinarith
  have hc1 : (39501757581/40000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (39501757581/40000000000:ℝ) ≤ taylorCos (395000053/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (493921915361/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1560825451/10000000000:ℝ) + taylorErr ≤ (493921915361/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (77724786701/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (77724786701/500000000000:ℝ) ≤ taylorSin (1560825451/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (78671728963/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (395000053/2500000000:ℝ) + taylorErr ≤ (78671728963/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-493921915361/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-39501757581/40000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-78671728963/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-77724786701/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3297675198757/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3299592674743/1000000000000:ℝ) := by nlinarith
  have hp1 : (272882388793/50000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5460821269149/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-214806125401/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-169677803707/200000000000:ℝ) := by nlinarith
  have hN : (128319437921/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (5193655909609/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (128319437921/1000000000000:ℝ) (5193655909609/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (76304221/2000000000000:ℝ) ≤ ((128319437921/1000000000000:ℝ)/(5193655909609/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_83 (x : ℝ) (h₁ : (17203/16384:ℝ) ≤ x) (h₂ : x ≤ (2151/2048:ℝ)) : (76304221/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1570412831/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (395000053/2500000000:ℝ) := by nlinarith
  have hc1 : (39501757581/40000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (39501757581/40000000000:ℝ) ≤ taylorCos (395000053/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (987694341327/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1570412831/10000000000:ℝ) + taylorErr ≤ (987694341327/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (156396585231/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (156396585231/1000000000000:ℝ) ≤ taylorSin (1570412831/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (78671728963/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (395000053/2500000000:ℝ) + taylorErr ≤ (78671728963/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-987694341327/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-39501757581/40000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-78671728963/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-156396585231/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3298633936749/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3299592674743/1000000000000:ℝ) := by nlinarith
  have hp1 : (5459234485877/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5460821269149/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-214806125401/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-426902815783/500000000000:ℝ) := by nlinarith
  have hN : (128319437921/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (5193655909609/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (128319437921/1000000000000:ℝ) (5193655909609/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (76304221/2000000000000:ℝ) ≤ ((128319437921/1000000000000:ℝ)/(5193655909609/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_84 (x : ℝ) (h₁ : (2151/2048:ℝ) ≤ x) (h₂ : x ≤ (8609/8192:ℝ)) : (31733701/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1580000211/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (399793743/2500000000:ℝ) := by nlinarith
  have hc1 : (15425631593/15625000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (15425631593/15625000000:ℝ) ≤ taylorCos (399793743/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (197508788813/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1580000211/10000000000:ℝ) + taylorErr ≤ (197508788813/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (157343453303/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (157343453303/1000000000000:ℝ) ≤ taylorSin (1580000211/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (159236759319/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (399793743/2500000000:ℝ) + taylorErr ≤ (159236759319/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-197508788813/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-15425631593/15625000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-159236759319/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-157343453303/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1649796337371/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3301510150727/1000000000000:ℝ) := by nlinarith
  have hp1 : (1092164239179/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (218559787569/40000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-870068807249/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-13425382263/15625000000:ℝ) := by nlinarith
  have hN : (117171614703/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20799938550707/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (117171614703/1000000000000:ℝ) (20799938550707/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (31733701/1000000000000:ℝ) ≤ ((117171614703/1000000000000:ℝ)/(20799938550707/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_85 (x : ℝ) (h₁ : (2151/2048:ℝ) ≤ x) (h₂ : x ≤ (4307/4096:ℝ)) : (259133459/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1580000211/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (404587433/2500000000:ℝ) := by nlinarith
  have hc1 : (986933274579/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (986933274579/1000000000000:ℝ) ≤ taylorCos (404587433/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (197508788813/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1580000211/10000000000:ℝ) + taylorErr ≤ (197508788813/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (157343453303/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (157343453303/1000000000000:ℝ) ≤ taylorSin (1580000211/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (32225895049/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (404587433/2500000000:ℝ) + taylorErr ≤ (32225895049/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-197508788813/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-986933274579/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-32225895049/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-157343453303/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1649796337371/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (412928453339/125000000000:ℝ) := by nlinarith
  have hp1 : (1092164239179/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5467168109303/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-880921928529/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-13425382263/15625000000:ℝ) := by nlinarith
  have hN : (2120226921/20000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20825268169849/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2120226921/20000000000:ℝ) (20825268169849/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (259133459/10000000000000:ℝ) ≤ ((2120226921/20000000000:ℝ)/(20825268169849/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_86 (x : ℝ) (h₁ : (2151/2048:ℝ) ≤ x) (h₂ : x ≤ (539/512:ℝ)) : (160574441/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1580000211/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1656699251/10000000000:ℝ) := by nlinarith
  have hc1 : (986308094981/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (986308094981/1000000000000:ℝ) ≤ taylorCos (1656699251/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (197508788813/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1580000211/10000000000:ℝ) + taylorErr ≤ (197508788813/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (157343453303/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (157343453303/1000000000000:ℝ) ≤ taylorSin (1580000211/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (4122828069/25000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1656699251/10000000000:ℝ) + taylorErr ≤ (4122828069/25000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-197508788813/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-986308094981/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-4122828069/25000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-157343453303/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1649796337371/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1653631289341/500000000000:ℝ) := by nlinarith
  have hp1 : (1092164239179/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2736757474729/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-902654442789/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-13425382263/15625000000:ℝ) := by nlinarith
  have hN : (2614176631/31250000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20875971528701/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2614176631/31250000000:ℝ) (20875971528701/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (160574441/10000000000000:ℝ) ≤ ((2614176631/31250000000:ℝ)/(20875971528701/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_87 (x : ℝ) (h₁ : (8609/8192:ℝ) ≤ x) (h₂ : x ≤ (4307/4096:ℝ)) : (259133459/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1599174971/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (404587433/2500000000:ℝ) := by nlinarith
  have hc1 : (986933274579/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (986933274579/1000000000000:ℝ) ≤ taylorCos (404587433/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (246810106623/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1599174971/10000000000:ℝ) + taylorErr ≤ (246810106623/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (19904594337/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (19904594337/125000000000:ℝ) ≤ taylorSin (1599174971/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (32225895049/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (404587433/2500000000:ℝ) + taylorErr ≤ (32225895049/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-246810106623/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-986933274579/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-32225895049/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-19904594337/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1650755075363/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (412928453339/125000000000:ℝ) := by nlinarith
  have hp1 : (5463994615929/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5467168109303/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-880921928529/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-217517192579/250000000000:ℝ) := by nlinarith
  have hN : (2120226921/20000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20825268169849/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2120226921/20000000000:ℝ) (20825268169849/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (259133459/10000000000000:ℝ) ≤ ((2120226921/20000000000:ℝ)/(20825268169849/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_88 (x : ℝ) (h₁ : (4307/4096:ℝ) ≤ x) (h₂ : x ≤ (8619/8192:ℝ)) : (25860883/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1618349731/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (409381123/2500000000:ℝ) := by nlinarith
  have hc1 : (123327812317/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (123327812317/125000000000:ℝ) ≤ taylorCos (409381123/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (986933279119/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1618349731/10000000000:ℝ) + taylorErr ≤ (986933279119/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (80564735311/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (80564735311/500000000000:ℝ) ≤ taylorSin (1618349731/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (20377699843/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (409381123/2500000000:ℝ) + taylorErr ≤ (20377699843/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-986933279119/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-123327812317/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-20377699843/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-80564735311/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3303427626711/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3305345102697/1000000000000:ℝ) := by nlinarith
  have hp1 : (1366792008991/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (273517076469/50000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-222945955449/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-220230472859/250000000000:ℝ) := by nlinarith
  have hN : (4741933837/50000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20850612495847/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4741933837/50000000000:ℝ) (20850612495847/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (25860883/1250000000000:ℝ) ≤ ((4741933837/50000000000:ℝ)/(20850612495847/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_89 (x : ℝ) (h₁ : (4307/4096:ℝ) ≤ x) (h₂ : x ≤ (539/512:ℝ)) : (160574441/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1618349731/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1656699251/10000000000:ℝ) := by nlinarith
  have hc1 : (986308094981/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (986308094981/1000000000000:ℝ) ≤ taylorCos (1656699251/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (986933279119/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1618349731/10000000000:ℝ) + taylorErr ≤ (986933279119/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (80564735311/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (80564735311/500000000000:ℝ) ≤ taylorSin (1618349731/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (4122828069/25000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1656699251/10000000000:ℝ) + taylorErr ≤ (4122828069/25000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-986933279119/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-986308094981/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-4122828069/25000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-80564735311/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3303427626711/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1653631289341/500000000000:ℝ) := by nlinarith
  have hp1 : (1366792008991/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2736757474729/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-902654442789/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-220230472859/250000000000:ℝ) := by nlinarith
  have hN : (2614176631/31250000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20875971528701/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2614176631/31250000000:ℝ) (20875971528701/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (160574441/10000000000000:ℝ) ≤ ((2614176631/31250000000:ℝ)/(20875971528701/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_90 (x : ℝ) (h₁ : (8619/8192:ℝ) ≤ x) (h₂ : x ≤ (539/512:ℝ)) : (160574441/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1637524491/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1656699251/10000000000:ℝ) := by nlinarith
  have hc1 : (986308094981/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (986308094981/1000000000000:ℝ) ≤ taylorCos (1656699251/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (246655625769/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1637524491/10000000000:ℝ) + taylorErr ≤ (246655625769/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (163021594121/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (163021594121/1000000000000:ℝ) ≤ taylorSin (1637524491/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (4122828069/25000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1656699251/10000000000:ℝ) + taylorErr ≤ (4122828069/25000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-246655625769/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-986308094981/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-4122828069/25000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-163021594121/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (413168137837/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1653631289341/500000000000:ℝ) := by nlinarith
  have hp1 : (5470341455999/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2736757474729/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-902654442789/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-891783784543/1000000000000:ℝ) := by nlinarith
  have hN : (2614176631/31250000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20875971528701/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2614176631/31250000000:ℝ) (20875971528701/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (160574441/10000000000000:ℝ) ≤ ((2614176631/31250000000:ℝ)/(20875971528701/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_91 (x : ℝ) (h₁ : (539/512:ℝ) ≤ x) (h₂ : x ≤ (8629/8192:ℝ)) : (60086101/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (6626797/40000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1675874011/10000000000:ℝ) := by nlinarith
  have hc1 : (492995032519/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (492995032519/500000000000:ℝ) ≤ taylorCos (1675874011/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (493154049761/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (6626797/40000000:ℝ) + taylorErr ≤ (493154049761/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (164913118137/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (164913118137/1000000000000:ℝ) ≤ taylorSin (6626797/40000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (166804040537/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1675874011/10000000000:ℝ) + taylorErr ≤ (166804040537/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-493154049761/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-492995032519/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-166804040537/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-164913118137/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3307262578681/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3309180054667/1000000000000:ℝ) := by nlinarith
  have hp1 : (2736757438017/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1095337673907/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-913533748801/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-3525993771/3906250000:ℝ) := by nlinarith
  have hN : (72456316237/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (5225336317103/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (72456316237/1000000000000:ℝ) (5225336317103/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (60086101/5000000000000:ℝ) ≤ ((72456316237/1000000000000:ℝ)/(5225336317103/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_92 (x : ℝ) (h₁ : (539/512:ℝ) ≤ x) (h₂ : x ≤ (4317/4096:ℝ)) : (85656967/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (6626797/40000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1695048771/10000000000:ℝ) := by nlinarith
  have hc1 : (985668409893/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (985668409893/1000000000000:ℝ) ≤ taylorCos (1695048771/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (493154049761/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (6626797/40000000:ℝ) + taylorErr ≤ (493154049761/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (164913118137/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (164913118137/1000000000000:ℝ) ≤ taylorSin (6626797/40000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (2635849141/15625000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1695048771/10000000000:ℝ) + taylorErr ≤ (2635849141/15625000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-493154049761/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-985668409893/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-2635849141/15625000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-164913118137/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3307262578681/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (827774382663/250000000000:ℝ) := by nlinarith
  have hp1 : (2736757438017/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5479861789613/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-924421695421/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-3525993771/3906250000:ℝ) := by nlinarith
  have hN : (7655839309/125000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (1046336685749/50000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (7655839309/125000000000:ℝ) (1046336685749/50000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (85656967/10000000000000:ℝ) ≤ ((7655839309/125000000000:ℝ)/(1046336685749/50000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_93 (x : ℝ) (h₁ : (539/512:ℝ) ≤ x) (h₂ : x ≤ (2161/2048:ℝ)) : (6838799/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (6626797/40000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1733398291/10000000000:ℝ) := by nlinarith
  have hc1 : (492507114369/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (492507114369/500000000000:ℝ) ≤ taylorCos (1733398291/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (493154049761/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (6626797/40000000:ℝ) + taylorErr ≤ (493154049761/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (164913118137/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (164913118137/1000000000000:ℝ) ≤ taylorSin (6626797/40000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (172473086327/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1733398291/10000000000:ℝ) + taylorErr ≤ (172473086327/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-493154049761/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-492507114369/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-172473086327/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-164913118137/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3307262578681/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3314932482621/1000000000000:ℝ) := by nlinarith
  have hp1 : (2736757438017/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5486208629767/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-94622333461/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-3525993771/3906250000:ℝ) := by nlinarith
  have hN : (2424430883/62500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (655548585271/31250000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2424430883/62500000000:ℝ) (655548585271/31250000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (6838799/2000000000000:ℝ) ≤ ((2424430883/62500000000:ℝ)/(655548585271/31250000000:ℝ))^2 := by norm_num
  linarith

theorem wc_94 (x : ℝ) (h₁ : (8629/8192:ℝ) ≤ x) (h₂ : x ≤ (4317/4096:ℝ)) : (85656967/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (167587401/1000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1695048771/10000000000:ℝ) := by nlinarith
  have hc1 : (985668409893/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (985668409893/1000000000000:ℝ) ≤ taylorCos (1695048771/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (985990069579/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (167587401/1000000000:ℝ) + taylorErr ≤ (985990069579/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (33360807183/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (33360807183/200000000000:ℝ) ≤ taylorSin (167587401/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (2635849141/15625000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1695048771/10000000000:ℝ) + taylorErr ≤ (2635849141/15625000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-985990069579/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-985668409893/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-2635849141/15625000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-33360807183/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1654590027333/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (827774382663/250000000000:ℝ) := by nlinarith
  have hp1 : (5476688296069/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5479861789613/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-924421695421/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-7136982119/7812500000:ℝ) := by nlinarith
  have hN : (7655839309/125000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (1046336685749/50000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (7655839309/125000000000:ℝ) (1046336685749/50000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (85656967/10000000000000:ℝ) ≤ ((7655839309/125000000000:ℝ)/(1046336685749/50000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_95 (x : ℝ) (h₁ : (4317/4096:ℝ) ≤ x) (h₂ : x ≤ (2161/2048:ℝ)) : (6838799/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (169504877/1000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1733398291/10000000000:ℝ) := by nlinarith
  have hc1 : (492507114369/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (492507114369/500000000000:ℝ) ≤ taylorCos (1733398291/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (492834207217/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (169504877/1000000000:ℝ) + taylorErr ≤ (492834207217/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (168694340401/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (168694340401/1000000000000:ℝ) ≤ taylorSin (169504877/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (172473086327/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1733398291/10000000000:ℝ) + taylorErr ≤ (172473086327/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-492834207217/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-492507114369/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-172473086327/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-168694340401/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3311097530651/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3314932482621/1000000000000:ℝ) := by nlinarith
  have hp1 : (684982714513/125000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5486208629767/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-94622333461/100000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-462210828843/500000000000:ℝ) := by nlinarith
  have hN : (2424430883/62500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (655548585271/31250000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2424430883/62500000000:ℝ) (655548585271/31250000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (6838799/2000000000000:ℝ) ≤ ((2424430883/62500000000:ℝ)/(655548585271/31250000000:ℝ))^2 := by norm_num
  linarith

theorem wc_96 (x : ℝ) (h₁ : (2161/2048:ℝ) ≤ x) (h₂ : x ≤ (4327/4096:ℝ)) : (239941/400000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (173339829/1000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1771747811/10000000000:ℝ) := by nlinarith
  have hc1 : (492172780569/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (492172780569/500000000000:ℝ) ≤ taylorCos (1771747811/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (3078169479/3125000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (173339829/1000000000:ℝ) + taylorErr ≤ (3078169479/3125000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (21559135213/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (21559135213/125000000000:ℝ) ≤ taylorSin (173339829/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (22031161387/125000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1771747811/10000000000:ℝ) + taylorErr ≤ (22031161387/125000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (-492172780569/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-22031161387/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-21559135213/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (165746624131/50000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3318767434591/1000000000000:ℝ) := by nlinarith
  have hp1 : (1371552139043/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2746277734961/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-24201475197/25000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-946223296553/1000000000000:ℝ) := by nlinarith
  have hN : (8143276629/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (5257108642451/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (8143276629/500000000000:ℝ) (5257108642451/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (239941/400000000000:ℝ) ≤ ((8143276629/500000000000:ℝ)/(5257108642451/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_97 (x : ℝ) (h₁ : (1083/1024:ℝ) ≤ x) (h₂ : x ≤ (2171/2048:ℝ)) : (875097/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1810097329/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (188679637/1000000000:ℝ) := by nlinarith
  have hc1 : (982252739087/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (982252739087/1000000000000:ℝ) ≤ taylorCos (188679637/1000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (983662421487/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1810097329/10000000000:ℝ) + taylorErr ≤ (983662421487/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (90011449537/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (90011449537/500000000000:ℝ) ≤ taylorSin (1810097329/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (187562130933/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (188679637/1000000000:ℝ) + taylorErr ≤ (187562130933/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-983662421487/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-982252739087/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-187562130933/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-90011449537/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (5191566229/1562500000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6660544581/2000000000:ℝ) := by nlinarith
  have hp1 : (5498902236313/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2755797995193/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1033766688799/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-197985664461/200000000000:ℝ) := by nlinarith
  have hN : (3132950409/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (4236285411549/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3132950409/500000000000:ℝ) (4236285411549/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (875097/10000000000000:ℝ) ≤ ((3132950409/500000000000:ℝ)/(4236285411549/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_98 (x : ℝ) (h₁ : (1083/1024:ℝ) ≤ x) (h₂ : x ≤ (17/16:ℝ)) : (433353/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1810097329/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1963495409/10000000000:ℝ) := by nlinarith
  have hc1 : (980785278131/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (980785278131/1000000000000:ℝ) ≤ taylorCos (1963495409/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (983662421487/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1810097329/10000000000:ℝ) + taylorErr ≤ (983662421487/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (90011449537/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (90011449537/500000000000:ℝ) ≤ taylorSin (1810097329/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-983662421487/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-980785278131/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-24386290541/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-90011449537/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (5191566229/1562500000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (83448554861/25000000000:ℝ) := by nlinarith
  have hp1 : (5498902236313/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (690536208837/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-538867731769/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-197985664461/200000000000:ℝ) := by nlinarith
  have hN : (3132950409/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10641858093423/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (3132950409/500000000000:ℝ) (10641858093423/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (433353/5000000000000:ℝ) ≤ ((3132950409/500000000000:ℝ)/(10641858093423/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_99 (x : ℝ) (h₁ : (2171/2048:ℝ) ≤ x) (h₂ : x ≤ (17/16:ℝ)) : (5858063/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1886796369/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (1963495409/10000000000:ℝ) := by nlinarith
  have hc1 : (980785278131/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (980785278131/1000000000000:ℝ) ≤ taylorCos (1963495409/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (98225274363/100000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1886796369/10000000000:ℝ) + taylorErr ≤ (98225274363/100000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (187562126311/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (187562126311/1000000000000:ℝ) ≤ taylorSin (1886796369/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-98225274363/100000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-980785278131/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-24386290541/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-187562126311/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3330272290499/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (83448554861/25000000000:ℝ) := by nlinarith
  have hp1 : (5511595916451/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (690536208837/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-538867731769/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-64610415591/62500000000:ℝ) := by nlinarith
  have hN : (25756952913/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10641858093423/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (25756952913/500000000000:ℝ) (10641858093423/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (5858063/1000000000000:ℝ) ≤ ((25756952913/500000000000:ℝ)/(10641858093423/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_100 (x : ℝ) (h₁ : (17/16:ℝ) ≤ x) (h₂ : x ≤ (1093/1024:ℝ)) : (40709377/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/625000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (132305843/625000000:ℝ) := by nlinarith
  have hc1 : (977677355547/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (977677355547/1000000000000:ℝ) ≤ taylorCos (132305843/625000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (39231411307/40000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/625000000:ℝ) + taylorErr ≤ (39231411307/40000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (97545159853/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (97545159853/500000000000:ℝ) ≤ taylorSin (122718463/625000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (210111839213/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (132305843/625000000:ℝ) + taylorErr ≤ (210111839213/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (-977677355547/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-210111839213/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-97545159853/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3337942194439/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3353282002319/1000000000000:ℝ) := by nlinarith
  have hp1 : (5524289596591/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1109935406263/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-145756606011/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1077735423547/1000000000000:ℝ) := by nlinarith
  have hN : (12118767609/125000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (10744500187077/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (12118767609/125000000000:ℝ) (10744500187077/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (40709377/2000000000000:ℝ) ≤ ((12118767609/125000000000:ℝ)/(10744500187077/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_101 (x : ℝ) (h₁ : (17/16:ℝ) ≤ x) (h₂ : x ≤ (549/512:ℝ)) : (9984781/500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/625000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (2270291567/10000000000:ℝ) := by nlinarith
  have hc1 : (974339380503/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (974339380503/1000000000000:ℝ) ≤ taylorCos (2270291567/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (39231411307/40000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/625000000:ℝ) + taylorErr ≤ (39231411307/40000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (97545159853/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (97545159853/500000000000:ℝ) ≤ taylorSin (122718463/625000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (14067744607/62500000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2270291567/10000000000:ℝ) + taylorErr ≤ (14067744607/62500000000:ℝ) := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (-974339380503/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-14067744607/62500000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-97545159853/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3337942194439/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3368621810197/1000000000000:ℝ) := by nlinarith
  have hp1 : (5524289596591/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5575064391933/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1254857312533/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1077735423547/1000000000000:ℝ) := by nlinarith
  have hN : (12118767609/125000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (2169522580027/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (12118767609/125000000000:ℝ) (2169522580027/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (9984781/500000000000:ℝ) ≤ ((12118767609/125000000000:ℝ)/(2169522580027/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_102 (x : ℝ) (h₁ : (17/16:ℝ) ≤ x) (h₂ : x ≤ (277/256:ℝ)) : (38452957/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/625000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (644271931/2500000000:ℝ) := by nlinarith
  have hc1 : (483488234387/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (483488234387/500000000000:ℝ) ≤ taylorCos (644271931/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (39231411307/40000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/625000000:ℝ) + taylorErr ≤ (39231411307/40000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (97545159853/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (97545159853/500000000000:ℝ) ≤ taylorSin (122718463/625000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (254865661901/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (644271931/2500000000:ℝ) + taylorErr ≤ (254865661901/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (-483488234387/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-254865661901/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-97545159853/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3337942194439/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (679860285191/200000000000:ℝ) := by nlinarith
  have hp1 : (5524289596591/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1406459778293/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-89614575583/62500000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1077735423547/1000000000000:ℝ) := by nlinarith
  have hN : (12118767609/125000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (22110500369/1000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (12118767609/125000000000:ℝ) (22110500369/1000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (38452957/2000000000000:ℝ) ≤ ((12118767609/125000000000:ℝ)/(22110500369/1000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_103 (x : ℝ) (h₁ : (17/16:ℝ) ≤ x) (h₂ : x ≤ (141/128:ℝ)) : (44604923/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/625000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (3190680039/10000000000:ℝ) := by nlinarith
  have hc1 : (37981127133/40000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (37981127133/40000000000:ℝ) ≤ taylorCos (3190680039/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (39231411307/40000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/625000000:ℝ) + taylorErr ≤ (39231411307/40000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (97545159853/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (97545159853/500000000000:ℝ) ≤ taylorSin (122718463/625000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (7842043567/25000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3190680039/10000000000:ℝ) + taylorErr ≤ (7842043567/25000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (-37981127133/40000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-7842043567/25000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-97545159853/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3337942194439/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3460660657471/1000000000000:ℝ) := by nlinarith
  have hp1 : (5524289596591/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (44745223091/7812500000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-898288611571/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1077735423547/1000000000000:ℝ) := by nlinarith
  have hN : (12118767609/125000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (1434521523271/62500000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (12118767609/125000000000:ℝ) (1434521523271/62500000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (44604923/2500000000000:ℝ) ≤ ((12118767609/125000000000:ℝ)/(1434521523271/62500000000:ℝ))^2 := by norm_num
  linarith

theorem wc_104 (x : ℝ) (h₁ : (17/16:ℝ) ≤ x) (h₂ : x ≤ (73/64:ℝ)) : (15429929/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/625000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (441786467/1000000000:ℝ) := by nlinarith
  have hc1 : (903989290823/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (903989290823/1000000000000:ℝ) ≤ taylorCos (441786467/1000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (39231411307/40000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/625000000:ℝ) + taylorErr ≤ (39231411307/40000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (97545159853/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (97545159853/500000000000:ℝ) ≤ taylorSin (122718463/625000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (427555095773/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (441786467/1000000000:ℝ) + taylorErr ≤ (427555095773/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (-903989290823/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-427555095773/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-97545159853/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3337942194439/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3583379120501/1000000000000:ℝ) := by nlinarith
  have hp1 : (5524289596591/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5930487440599/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1267805062823/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1077735423547/1000000000000:ℝ) := by nlinarith
  have hN : (12118767609/125000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (12340605921243/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (12118767609/125000000000:ℝ) (12340605921243/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (15429929/1000000000000:ℝ) ≤ ((12118767609/125000000000:ℝ)/(12340605921243/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_105 (x : ℝ) (h₁ : (1093/1024:ℝ) ≤ x) (h₂ : x ≤ (549/512:ℝ)) : (753911279/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2116893487/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (2270291567/10000000000:ℝ) := by nlinarith
  have hc1 : (974339380503/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (974339380503/1000000000000:ℝ) ≤ taylorCos (2270291567/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (977677360093/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2116893487/10000000000:ℝ) + taylorErr ≤ (977677360093/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (210111834591/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (210111834591/1000000000000:ℝ) ≤ taylorSin (2116893487/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (14067744607/62500000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2270291567/10000000000:ℝ) + taylorErr ≤ (14067744607/62500000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-977677360093/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-974339380503/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-14067744607/62500000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-210111834591/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1676641001159/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3368621810197/1000000000000:ℝ) := by nlinarith
  have hp1 : (554967695687/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5575064391933/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1254857312533/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-233210561359/200000000000:ℝ) := by nlinarith
  have hN : (94187723351/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (2169522580027/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (94187723351/500000000000:ℝ) (2169522580027/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (753911279/10000000000000:ℝ) ≤ ((94187723351/500000000000:ℝ)/(2169522580027/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_106 (x : ℝ) (h₁ : (549/512:ℝ) ≤ x) (h₂ : x ≤ (277/256:ℝ)) : (1609622259/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1135145783/5000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (644271931/2500000000:ℝ) := by nlinarith
  have hc1 : (483488234387/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (483488234387/500000000000:ℝ) ≤ taylorCos (644271931/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (974339385049/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1135145783/5000000000:ℝ) + taylorErr ≤ (974339385049/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (225083909091/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (225083909091/1000000000000:ℝ) ≤ taylorSin (1135145783/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (254865661901/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (644271931/2500000000:ℝ) + taylorErr ≤ (254865661901/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-974339385049/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-483488234387/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-254865661901/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-225083909091/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (842155452549/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (679860285191/200000000000:ℝ) := by nlinarith
  have hp1 : (5575064317147/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1406459778293/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-89614575583/62500000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1254857269937/1000000000000:ℝ) := by nlinarith
  have hN : (35064735611/125000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (22110500369/1000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (35064735611/125000000000:ℝ) (22110500369/1000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (1609622259/10000000000000:ℝ) ≤ ((35064735611/125000000000:ℝ)/(22110500369/1000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_107 (x : ℝ) (h₁ : (277/256:ℝ) ≤ x) (h₂ : x ≤ (141/128:ℝ)) : (4137262453/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (2577087723/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (3190680039/10000000000:ℝ) := by nlinarith
  have hc1 : (37981127133/40000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (37981127133/40000000000:ℝ) ≤ taylorCos (3190680039/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (241744118331/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (2577087723/10000000000:ℝ) + taylorErr ≤ (241744118331/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (796455179/3125000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (796455179/3125000000:ℝ) ≤ taylorSin (2577087723/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (7842043567/25000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3190680039/10000000000:ℝ) + taylorErr ≤ (7842043567/25000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-241744118331/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-37981127133/40000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-7842043567/25000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-796455179/3125000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1699650712977/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3460660657471/1000000000000:ℝ) := by nlinarith
  have hp1 : (703229879713/125000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (44745223091/7812500000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-898288611571/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-286766632819/200000000000:ℝ) := by nlinarith
  have hN : (466856690771/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (1434521523271/62500000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (466856690771/1000000000000:ℝ) (1434521523271/62500000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (4137262453/10000000000000:ℝ) ≤ ((466856690771/1000000000000:ℝ)/(1434521523271/62500000000:ℝ))^2 := by norm_num
  linarith

theorem wc_108 (x : ℝ) (h₁ : (141/128:ℝ) ≤ x) (h₂ : x ≤ (73/64:ℝ)) : (11778340313/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1595340019/5000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (441786467/1000000000:ℝ) := by nlinarith
  have hc1 : (903989290823/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (903989290823/1000000000000:ℝ) ≤ taylorCos (441786467/1000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (5934551143/6250000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1595340019/5000000000:ℝ) + taylorErr ≤ (5934551143/6250000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (313681738061/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (313681738061/1000000000000:ℝ) ≤ taylorSin (1595340019/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (427555095773/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (441786467/1000000000:ℝ) + taylorErr ≤ (427555095773/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-5934551143/6250000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-903989290823/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-427555095773/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-313681738061/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (346066065747/100000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3583379120501/1000000000000:ℝ) := by nlinarith
  have hp1 : (5727388478819/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5930487440599/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1267805062823/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-898288586293/500000000000:ℝ) := by nlinarith
  have hN : (423524494853/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (12340605921243/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (423524494853/500000000000:ℝ) (12340605921243/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (11778340313/10000000000000:ℝ) ≤ ((423524494853/500000000000:ℝ)/(12340605921243/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_109 (x : ℝ) (h₁ : (73/64:ℝ) ≤ x) (h₂ : x ≤ (37/32:ℝ)) : (41297698399/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (4417864669/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (2454369261/5000000000:ℝ) := by nlinarith
  have hc1 : (17638425241/20000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (17638425241/20000000000:ℝ) ≤ taylorCos (2454369261/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (90398929539/100000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (4417864669/10000000000:ℝ) + taylorErr ≤ (90398929539/100000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (213777545579/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (213777545579/500000000000:ℝ) ≤ taylorSin (4417864669/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (117849184789/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2454369261/5000000000:ℝ) + taylorErr ≤ (117849184789/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-90398929539/100000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-17638425241/20000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-117849184789/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-213777545579/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (7166758241/2000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1816233252857/500000000000:ℝ) := by nlinarith
  have hp1 : (1186097472209/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (6011726994581/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1416954250971/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1267805032131/500000000000:ℝ) := by nlinarith
  have hN : (203952596109/125000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (25389625830269/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (203952596109/125000000000:ℝ) (25389625830269/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (41297698399/10000000000000:ℝ) ≤ ((203952596109/125000000000:ℝ)/(25389625830269/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_110 (x : ℝ) (h₁ : (37/32:ℝ) ≤ x) (h₂ : x ≤ (19/16:ℝ)) : (52910124749/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (4908738521/10000000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (2945243113/5000000000:ℝ) := by nlinarith
  have hc1 : (103933701251/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (103933701251/125000000000:ℝ) ≤ taylorCos (2945243113/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (881921266621/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (4908738521/10000000000:ℝ) + taylorErr ≤ (881921266621/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (471396734543/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (471396734543/1000000000000:ℝ) ≤ taylorSin (4908738521/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (1:ℝ))) ≤ (22222809413/40000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2945243113/5000000000:ℝ) + taylorErr ≤ (22222809413/40000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (-1:ℝ) * Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).1
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := (trig_shift (1:ℝ) (x - (1:ℝ))).2
    rw [show (1:ℝ) + (x - (1:ℝ)) = x by ring, cs_1.1, cs_1.2] at h
    rw [h]; ring
  have hcxl : (-881921266621/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-103933701251/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-22222809413/40000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-471396734543/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3632466505713/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1865320638069/500000000000:ℝ) := by nlinarith
  have hp1 : (3005863456969/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (6174206102541/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-1715102568667/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-1416954218097/500000000000:ℝ) := by nlinarith
  have hN : (1951987169573/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (536707373249/20000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1951987169573/1000000000000:ℝ) (536707373249/20000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (52910124749/10000000000000:ℝ) ≤ ((1951987169573/1000000000000:ℝ)/(536707373249/20000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_111 (x : ℝ) (h₁ : (19/16:ℝ) ≤ x) (h₂ : x ≤ (5/4:ℝ)) : (15166428823/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (235619449/400000000:ℝ) ≤ Real.pi * (x - (1:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (1:ℝ)) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (1:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (1:ℝ))) ≤ (207867403647/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (235619449/400000000:ℝ) + taylorErr ≤ (207867403647/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (555570230717/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (1:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (555570230717/1000000000000:ℝ) ≤ taylorSin (235619449/400000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxl : (-207867403647/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (-88388347351/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-176776695861/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-555570230717/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3730641276137/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (981747704247/250000000000:ℝ) := by nlinarith
  have hp1 : (6174206019719/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (3249582159233/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-919120635261/200000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-3430205062869/1000000000000:ℝ) := by nlinarith
  have hN : (2598735448281/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (29842513753417/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2598735448281/1000000000000:ℝ) (29842513753417/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (15166428823/2000000000000:ℝ) ≤ ((2598735448281/1000000000000:ℝ)/(29842513753417/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_112 (x : ℝ) (h₁ : (5/4:ℝ) ≤ x) (h₂ : x ≤ (3/2:ℝ)) : (20056696131/2500000000000:ℝ) ≤ wfun x := by
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

theorem wc_113 (x : ℝ) (h₁ : (3/2:ℝ) ≤ x) (h₂ : x ≤ (7/4:ℝ)) : (86044756753/10000000000000:ℝ) ≤ wfun x := by
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

theorem wc_114 (x : ℝ) (h₁ : (7/4:ℝ) ≤ x) (h₂ : x ≤ (15/8:ℝ)) : (1500513453/400000000000:ℝ) ≤ wfun x := by
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

theorem wc_115 (x : ℝ) (h₁ : (15/8:ℝ) ≤ x) (h₂ : x ≤ (121/64:ℝ)) : (18300645841/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (859029241/2500000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (3926990817/10000000000:ℝ) := by nlinarith
  have hc1 : (923879530249/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (923879530249/1000000000000:ℝ) ≤ taylorCos (3926990817/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (470772033737/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (859029241/2500000000:ℝ) + taylorErr ≤ (470772033737/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (336889851049/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (336889851049/1000000000000:ℝ) ≤ taylorSin (859029241/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (470772033737/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-95670858657/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-336889851049/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (147262155637/25000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2969786805347/500000000000:ℝ) := by nlinarith
  have hp1 : (389949853877/40000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (4914993015839/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-940443204237/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-328425370473/100000000000:ℝ) := by nlinarith
  have hN : (4208133234979/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (34778534676853/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (4208133234979/1000000000000:ℝ) (34778534676853/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (18300645841/5000000000000:ℝ) ≤ ((4208133234979/1000000000000:ℝ)/(34778534676853/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_116 (x : ℝ) (h₁ : (121/64:ℝ) ≤ x) (h₂ : x ≤ (247/128:ℝ)) : (9113139537/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1104466167/5000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (687223393/2000000000:ℝ) := by nlinarith
  have hc1 : (235386015729/250000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (235386015729/250000000000:ℝ) ≤ taylorCos (687223393/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (975702132313/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1104466167/5000000000:ℝ) + taylorErr ≤ (975702132313/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (219101237841/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (219101237841/1000000000000:ℝ) ≤ taylorSin (1104466167/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (336889855667/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (687223393/2000000000:ℝ) + taylorErr ≤ (336889855667/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (235386015729/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (975702132313/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-336889855667/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-219101237841/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (5939573610693/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (242491682949/40000000000:ℝ) := by nlinarith
  have hp1 : (9829985899817/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10033084916631/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-3380044529459/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-2153762078609/1000000000000:ℝ) := by nlinarith
  have hN : (123812245661/40000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (36251385187149/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (123812245661/40000000000:ℝ) (36251385187149/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (9113139537/5000000000000:ℝ) ≤ ((123812245661/40000000000:ℝ)/(36251385187149/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_117 (x : ℝ) (h₁ : (121/64:ℝ) ≤ x) (h₂ : x ≤ (63/32:ℝ)) : (795663039/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/1250000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (687223393/2000000000:ℝ) := by nlinarith
  have hc1 : (235386015729/250000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (235386015729/250000000000:ℝ) ≤ taylorCos (687223393/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (995184728937/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/1250000000:ℝ) + taylorErr ≤ (995184728937/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (98017138043/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (98017138043/1000000000000:ℝ) ≤ taylorSin (122718463/1250000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (336889855667/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (687223393/2000000000:ℝ) + taylorErr ≤ (336889855667/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (235386015729/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (995184728937/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-336889855667/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-98017138043/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (5939573610693/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1237002107351/200000000000:ℝ) := by nlinarith
  have hp1 : (9829985899817/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10236183801581/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-431058310437/125000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-963507084903/1000000000000:ℝ) := by nlinarith
  have hN : (1905051147819/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (75508710679541/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1905051147819/1000000000000:ℝ) (75508710679541/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (795663039/1250000000000:ℝ) ≤ ((1905051147819/1000000000000:ℝ)/(75508710679541/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_118 (x : ℝ) (h₁ : (247/128:ℝ) ≤ x) (h₂ : x ≤ (499/256:ℝ)) : (6028900351/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1595340019/10000000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (441786467/2000000000:ℝ) := by nlinarith
  have hc1 : (975702127767/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (975702127767/1000000000000:ℝ) ≤ taylorCos (441786467/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (493650710213/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1595340019/10000000000:ℝ) + taylorErr ≤ (493650710213/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (19857267629/125000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (19857267629/125000000000:ℝ) ≤ taylorSin (1595340019/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (109550621231/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (441786467/2000000000:ℝ) + taylorErr ≤ (109550621231/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (975702127767/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (493650710213/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-109550621231/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-19857267629/125000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1515573018431/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (153091282631/25000000000:ℝ) := by nlinarith
  have hp1 : (2006616956409/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5067317179553/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-2220510979979/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-398459299323/250000000000:ℝ) := by nlinarith
  have hN : (2569539325059/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (4624888163521/62500000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2569539325059/1000000000000:ℝ) (4624888163521/62500000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (6028900351/5000000000000:ℝ) ≤ ((2569539325059/1000000000000:ℝ)/(4624888163521/62500000000:ℝ))^2 := by norm_num
  linarith

theorem wc_119 (x : ℝ) (h₁ : (247/128:ℝ) ≤ x) (h₂ : x ≤ (63/32:ℝ)) : (6731724963/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (122718463/1250000000:ℝ) ≤ Real.pi * ((2:ℝ) - x) := by nlinarith
  have ht2 : Real.pi * ((2:ℝ) - x) ≤ (441786467/2000000000:ℝ) := by nlinarith
  have hc1 : (975702127767/1000000000000:ℝ) ≤ Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (975702127767/1000000000000:ℝ) ≤ taylorCos (441786467/2000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * ((2:ℝ) - x)) ≤ (995184728937/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (122718463/1250000000:ℝ) + taylorErr ≤ (995184728937/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (98017138043/1000000000000:ℝ) ≤ Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (98017138043/1000000000000:ℝ) ≤ taylorSin (122718463/1250000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * ((2:ℝ) - x)) ≤ (109550621231/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (441786467/2000000000:ℝ) + taylorErr ≤ (109550621231/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).1
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hsx : Real.sin (Real.pi*x) = (-1:ℝ) * Real.sin (Real.pi * ((2:ℝ) - x)) := by
    have h := (trig_shift (2:ℝ) (x - (2:ℝ))).2
    rw [show (2:ℝ) + (x - (2:ℝ)) = x by ring, cs_2.1, cs_2.2] at h
    rw [h, cos_flip (2:ℝ) x, sin_flip (2:ℝ) x]; ring
  have hcxl : (975702127767/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (995184728937/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (-109550621231/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (-98017138043/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1515573018431/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (1237002107351/200000000000:ℝ) := by nlinarith
  have hp1 : (2006616956409/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10236183801581/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (-560690147249/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (-491707128039/500000000000:ℝ) := by nlinarith
  have hN : (391823276769/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_le (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (75508710679541/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (391823276769/200000000000:ℝ) (75508710679541/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (6731724963/10000000000000:ℝ) ≤ ((391823276769/200000000000:ℝ)/(75508710679541/1000000000000:ℝ))^2 := by norm_num
  linarith

end Zeta23Ext.Bridge.FourPoint
