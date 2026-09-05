import FourPoint.Base

noncomputable section
open Real
namespace Zeta23Ext.Bridge.FourPoint


theorem wc_780 (x : ℝ) (h₁ : (16523/4096:ℝ) ≤ x) (h₂ : x ≤ (8287/2048:ℝ)) : (36879733/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1066116647/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1457281749/10000000000:ℝ) := by nlinarith
  have hc1 : (494700212761/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (494700212761/500000000000:ℝ) ≤ taylorCos (1457281749/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (994322359491/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1066116647/10000000000:ℝ) + taylorErr ≤ (994322359491/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (53204909157/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (53204909157/500000000000:ℝ) ≤ taylorSin (1066116647/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (29042585393/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1457281749/10000000000:ℝ) + taylorErr ≤ (29042585393/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (494700212761/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (994322359491/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (53204909157/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (29042585393/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12672982279117/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12712098789209/1000000000000:ℝ) := by nlinarith
  have hp1 : (4194753538809/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21038505744967/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2231814809683/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (3055062998197/1000000000000:ℝ) := by nlinarith
  have hN : (77343278137/62500000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (161097455626609/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (77343278137/62500000000:ℝ) (161097455626609/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (36879733/2500000000000:ℝ) ≤ ((77343278137/62500000000:ℝ)/(161097455626609/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_781 (x : ℝ) (h₁ : (1033/256:ℝ) ≤ x) (h₂ : x ≤ (519/128:ℝ)) : (8305511/500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1104466167/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1718058483/10000000000:ℝ) := by nlinarith
  have hc1 : (985277640117/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (985277640117/1000000000000:ℝ) ≤ taylorCos (1718058483/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (248476743067/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1104466167/10000000000:ℝ) + taylorErr ≤ (248476743067/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (27555551251/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (27555551251/250000000000:ℝ) ≤ taylorSin (1104466167/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (85480945539/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1718058483/10000000000:ℝ) + taylorErr ≤ (85480945539/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (985277640117/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (248476743067/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (27555551251/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (85480945539/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6338408615543/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12738176462603/1000000000000:ℝ) := by nlinarith
  have hp1 : (10490057267057/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21081664258019/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1156237242593/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (3604161188623/1000000000000:ℝ) := by nlinarith
  have hN : (659283756459/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (323522279184827/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (659283756459/500000000000:ℝ) (323522279184827/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (8305511/500000000000:ℝ) ≤ ((659283756459/500000000000:ℝ)/(323522279184827/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_782 (x : ℝ) (h₁ : (1033/256:ℝ) ≤ x) (h₂ : x ≤ (4157/1024:ℝ)) : (165310021/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1104466167/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (935728281/5000000000:ℝ) := by nlinarith
  have hc1 : (982539300011/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (982539300011/1000000000000:ℝ) ≤ taylorCos (935728281/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (248476743067/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1104466167/10000000000:ℝ) + taylorErr ≤ (248476743067/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (27555551251/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (27555551251/250000000000:ℝ) ≤ taylorSin (1104466167/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (93027577001/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (935728281/5000000000:ℝ) + taylorErr ≤ (93027577001/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (982539300011/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (248476743067/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (27555551251/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (93027577001/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6338408615543/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6376758135241/500000000000:ℝ) := by nlinarith
  have hp1 : (10490057267057/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10553525809319/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1156237242593/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1963537869717/500000000000:ℝ) := by nlinarith
  have hN : (659283756459/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (324304354522899/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (659283756459/500000000000:ℝ) (324304354522899/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (165310021/10000000000000:ℝ) ≤ ((659283756459/500000000000:ℝ)/(324304354522899/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_783 (x : ℝ) (h₁ : (1033/256:ℝ) ≤ x) (h₂ : x ≤ (2081/512:ℝ)) : (164514637/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1104466167/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2024854641/10000000000:ℝ) := by nlinarith
  have hc1 : (979569763403/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (979569763403/1000000000000:ℝ) ≤ taylorCos (2024854641/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (248476743067/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1104466167/10000000000:ℝ) + taylorErr ≤ (248476743067/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (27555551251/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (27555551251/250000000000:ℝ) ≤ taylorSin (1104466167/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (201104637201/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2024854641/10000000000:ℝ) + taylorErr ≤ (201104637201/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (979569763403/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (248476743067/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (27555551251/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (201104637201/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6338408615543/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12768856078361/1000000000000:ℝ) := by nlinarith
  have hp1 : (10490057267057/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21132438979257/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1156237242593/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (265614467131/62500000000:ℝ) := by nlinarith
  have hN : (659283756459/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (162543685549897/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (659283756459/500000000000:ℝ) (162543685549897/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (164514637/10000000000000:ℝ) ≤ ((659283756459/500000000000:ℝ)/(162543685549897/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_784 (x : ℝ) (h₁ : (1033/256:ℝ) ≤ x) (h₂ : x ≤ (1043/256:ℝ)) : (81469089/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1104466167/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1165825399/5000000000:ℝ) := by nlinarith
  have hc1 : (486469974967/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (486469974967/500000000000:ℝ) ≤ taylorCos (1165825399/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (248476743067/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1104466167/10000000000:ℝ) + taylorErr ≤ (248476743067/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (27555551251/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (27555551251/250000000000:ℝ) ≤ taylorSin (1104466167/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (248476743067/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (27555551251/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (231058110583/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6338408615543/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6399767847059/500000000000:ℝ) := by nlinarith
  have hp1 : (10490057267057/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10591606850247/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1156237242593/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (4894553333713/1000000000000:ℝ) := by nlinarith
  have hN : (659283756459/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (163328113985001/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (659283756459/500000000000:ℝ) (163328113985001/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (81469089/5000000000000:ℝ) ≤ ((659283756459/500000000000:ℝ)/(163328113985001/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_785 (x : ℝ) (h₁ : (1033/256:ℝ) ≤ x) (h₂ : x ≤ (2091/512:ℝ)) : (20172571/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1104466167/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (659611739/2500000000:ℝ) := by nlinarith
  have hc1 : (482697219707/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (482697219707/500000000000:ℝ) ≤ taylorCos (659611739/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (248476743067/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1104466167/10000000000:ℝ) + taylorErr ≤ (248476743067/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (27555551251/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (27555551251/250000000000:ℝ) ≤ taylorSin (1104466167/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (248476743067/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (27555551251/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (130397060129/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6338408615543/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3207553827469/250000000000:ℝ) := by nlinarith
  have hp1 : (10490057267057/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21233988421733/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1156237242593/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1107539866003/200000000000:ℝ) := by nlinarith
  have hN : (659283756459/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (164114424897777/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (659283756459/500000000000:ℝ) (164114424897777/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (20172571/1250000000000:ℝ) ≤ ((659283756459/500000000000:ℝ)/(164114424897777/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_786 (x : ℝ) (h₁ : (1033/256:ℝ) ≤ x) (h₂ : x ≤ (131/32:ℝ)) : (159841537/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1104466167/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2945243113/10000000000:ℝ) := by nlinarith
  have hc1 : (956940333463/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (956940333463/1000000000000:ℝ) ≤ taylorCos (2945243113/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (248476743067/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1104466167/10000000000:ℝ) + taylorErr ≤ (248476743067/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (27555551251/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (27555551251/250000000000:ℝ) ≤ taylorSin (1104466167/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (248476743067/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (27555551251/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (290284679541/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6338408615543/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6430447462817/500000000000:ℝ) := by nlinarith
  have hp1 : (10490057267057/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21284763142971/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1156237242593/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (48270630063/7812500000:ℝ) := by nlinarith
  have hN : (659283756459/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (329805236576397/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (659283756459/500000000000:ℝ) (329805236576397/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (159841537/10000000000000:ℝ) ≤ ((659283756459/500000000000:ℝ)/(329805236576397/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_787 (x : ℝ) (h₁ : (1033/256:ℝ) ≤ x) (h₂ : x ≤ (1053/256:ℝ)) : (39204539/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1104466167/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (889708857/2500000000:ℝ) := by nlinarith
  have hc1 : (937339009647/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (937339009647/1000000000000:ℝ) ≤ taylorCos (889708857/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (248476743067/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1104466167/10000000000:ℝ) + taylorErr ≤ (248476743067/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (27555551251/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (27555551251/250000000000:ℝ) ≤ taylorSin (1104466167/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (248476743067/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (27555551251/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (348418682521/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6338408615543/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12922254157149/1000000000000:ℝ) := by nlinarith
  have hp1 : (10490057267057/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10693156292723/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1156237242593/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1862847713751/250000000000:ℝ) := by nlinarith
  have hN : (659283756459/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (33296930500391/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (659283756459/500000000000:ℝ) (33296930500391/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (39204539/2500000000000:ℝ) ≤ ((659283756459/500000000000:ℝ)/(33296930500391/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_788 (x : ℝ) (h₁ : (1033/256:ℝ) ≤ x) (h₂ : x ≤ (529/128:ℝ)) : (153865963/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1104466167/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (130388367/312500000:ℝ) := by nlinarith
  have hc1 : (914209753403/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (914209753403/1000000000000:ℝ) ≤ taylorCos (130388367/312500000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (248476743067/250000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1104466167/10000000000:ℝ) + taylorErr ≤ (248476743067/250000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (27555551251/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (27555551251/250000000000:ℝ) ≤ taylorSin (1104466167/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (248476743067/250000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (27555551251/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (202620658177/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6338408615543/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2596722677733/200000000000:ℝ) := by nlinarith
  have hp1 : (10490057267057/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21487862027923/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1156237242593/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (8707769493829/1000000000000:ℝ) := by nlinarith
  have hN : (659283756459/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (336148433252643/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (659283756459/500000000000:ℝ) (336148433252643/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (153865963/10000000000000:ℝ) ≤ ((659283756459/500000000000:ℝ)/(336148433252643/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_789 (x : ℝ) (h₁ : (8265/2048:ℝ) ≤ x) (h₂ : x ≤ (2079/512:ℝ)) : (86688141/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (44792239/400000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1902136177/10000000000:ℝ) := by nlinarith
  have hc1 : (981963866847/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (981963866847/1000000000000:ℝ) ≤ taylorCos (1902136177/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (198747344841/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (44792239/400000000:ℝ) + taylorErr ≤ (198747344841/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (111746708933/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (111746708933/1000000000000:ℝ) ≤ taylorSin (44792239/400000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (94534333207/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1902136177/10000000000:ℝ) + taylorErr ≤ (94534333207/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (981963866847/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (198747344841/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (111746708933/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (94534333207/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6339175605937/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12756584232057/1000000000000:ℝ) := by nlinarith
  have hp1 : (10491326635071/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21112129090761/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (117237122381/50000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (3991642092351/1000000000000:ℝ) := by nlinarith
  have hN : (270201144683/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (324460882539131/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (270201144683/200000000000:ℝ) (324460882539131/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (86688141/5000000000000:ℝ) ≤ ((270201144683/200000000000:ℝ)/(324460882539131/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_790 (x : ℝ) (h₁ : (4133/1024:ℝ) ≤ x) (h₂ : x ≤ (16583/4096:ℝ)) : (22996019/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1135145783/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (381577721/2500000000:ℝ) := by nlinarith
  have hc1 : (494187234373/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (494187234373/500000000000:ℝ) ≤ taylorCos (381577721/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (993564137783/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1135145783/10000000000:ℝ) + taylorErr ≤ (993564137783/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (14158868739/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (14158868739/125000000000:ℝ) ≤ taylorSin (1135145783/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (38009789649/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (381577721/2500000000:ℝ) + taylorErr ≤ (38009789649/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (494187234373/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (993564137783/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (14158868739/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (38009789649/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6339942596331/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6359500851377/500000000000:ℝ) := by nlinarith
  have hp1 : (2098519200617/100000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5262482514311/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (148563289539/62500000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (3200413654409/1000000000000:ℝ) := by nlinarith
  have hN : (1383448494841/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (322546008629319/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1383448494841/1000000000000:ℝ) (322546008629319/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (22996019/1250000000000:ℝ) ≤ ((1383448494841/1000000000000:ℝ)/(322546008629319/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_791 (x : ℝ) (h₁ : (8267/2048:ℝ) ≤ x) (h₂ : x ≤ (4159/1024:ℝ)) : (95123723/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (115048559/1000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1932815793/10000000000:ℝ) := by nlinarith
  have hc1 : (981379191047/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (981379191047/1000000000000:ℝ) ≤ taylorCos (1932815793/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (993389213421/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (115048559/1000000000:ℝ) + taylorErr ≤ (993389213421/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (57397462127/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (57397462127/500000000000:ℝ) ≤ taylorSin (115048559/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (96040199669/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1932815793/10000000000:ℝ) + taylorErr ≤ (96040199669/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (981379191047/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (993389213421/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (57397462127/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (96040199669/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (253628383469/20000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12759652193633/1000000000000:ℝ) := by nlinarith
  have hp1 : (10493865371099/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (4223441312577/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2409284960813/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (2028100734751/500000000000:ℝ) := by nlinarith
  have hN : (22123371053/15625000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (324617448204967/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (22123371053/15625000000:ℝ) (324617448204967/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (95123723/5000000000000:ℝ) ≤ ((22123371053/15625000000:ℝ)/(324617448204967/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_792 (x : ℝ) (h₁ : (8267/2048:ℝ) ≤ x) (h₂ : x ≤ (4169/1024:ℝ)) : (188423087/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (115048559/1000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2239611951/10000000000:ℝ) := by nlinarith
  have hc1 : (97502534279/100000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (97502534279/100000000000:ℝ) ≤ taylorCos (2239611951/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (993389213421/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (115048559/1000000000:ℝ) + taylorErr ≤ (993389213421/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (57397462127/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (57397462127/500000000000:ℝ) ≤ taylorSin (115048559/1000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (111046811651/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2239611951/10000000000:ℝ) + taylorErr ≤ (111046811651/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (97502534279/100000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (993389213421/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (57397462127/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (111046811651/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (253628383469/20000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12790331809391/1000000000000:ℝ) := by nlinarith
  have hp1 : (10493865371099/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21167981284123/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2409284960813/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (235063683069/50000000000:ℝ) := by nlinarith
  have hN : (22123371053/15625000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (326185175588639/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (22123371053/15625000000:ℝ) (326185175588639/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (188423087/10000000000000:ℝ) ≤ ((22123371053/15625000000:ℝ)/(326185175588639/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_793 (x : ℝ) (h₁ : (16543/4096:ℝ) ≤ x) (h₂ : x ≤ (8307/2048:ℝ)) : (14547321/625000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (609757363/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1764077907/10000000000:ℝ) := by nlinarith
  have hc1 : (196896090621/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (196896090621/200000000000:ℝ) ≤ taylorCos (1764077907/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (992573132743/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (609757363/5000000000:ℝ) + taylorErr ≤ (992573132743/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (1216494147/10000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (1216494147/10000000000:ℝ) ≤ taylorSin (609757363/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (175494255731/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1764077907/10000000000:ℝ) + taylorErr ≤ (175494255731/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (196896090621/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (992573132743/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (1216494147/10000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (175494255731/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3172080521749/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12742778404967/1000000000000:ℝ) := by nlinarith
  have hp1 : (5249788763581/250000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (4217856093241/200000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2554534921553/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (3701047579319/1000000000000:ℝ) := by nlinarith
  have hN : (156196178881/100000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (323756802956187/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (156196178881/100000000000:ℝ) (323756802956187/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (14547321/625000000000:ℝ) ≤ ((156196178881/100000000000:ℝ)/(323756802956187/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_794 (x : ℝ) (h₁ : (4137/1024:ℝ) ≤ x) (h₂ : x ≤ (519/128:ℝ)) : (128977417/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (628932123/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1718058483/10000000000:ℝ) := by nlinarith
  have hc1 : (985277640117/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (985277640117/1000000000000:ℝ) ≤ taylorCos (1718058483/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (198419863081/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (628932123/5000000000:ℝ) + taylorErr ≤ (198419863081/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (125454981143/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (125454981143/1000000000000:ℝ) ≤ taylorSin (628932123/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (85480945539/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1718058483/10000000000:ℝ) + taylorErr ≤ (85480945539/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (985277640117/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (198419863081/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (125454981143/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (85480945539/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (2538431407793/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12738176462603/1000000000000:ℝ) := by nlinarith
  have hp1 : (21005501894393/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21081664258019/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (131762242203/50000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (3604161188623/1000000000000:ℝ) := by nlinarith
  have hN : (328629105731/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (323522279184827/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (328629105731/200000000000:ℝ) (323522279184827/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (128977417/5000000000000:ℝ) ≤ ((328629105731/200000000000:ℝ)/(323522279184827/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_795 (x : ℝ) (h₁ : (4137/1024:ℝ) ≤ x) (h₂ : x ≤ (4157/1024:ℝ)) : (128356097/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (628932123/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (935728281/5000000000:ℝ) := by nlinarith
  have hc1 : (982539300011/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (982539300011/1000000000000:ℝ) ≤ taylorCos (935728281/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (198419863081/200000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (628932123/5000000000:ℝ) + taylorErr ≤ (198419863081/200000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (125454981143/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (125454981143/1000000000000:ℝ) ≤ taylorSin (628932123/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (93027577001/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (935728281/5000000000:ℝ) + taylorErr ≤ (93027577001/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (982539300011/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (198419863081/200000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (125454981143/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (93027577001/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (2538431407793/200000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6376758135241/500000000000:ℝ) := by nlinarith
  have hp1 : (21005501894393/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10553525809319/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (131762242203/50000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1963537869717/500000000000:ℝ) := by nlinarith
  have hN : (328629105731/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (324304354522899/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (328629105731/200000000000:ℝ) (324304354522899/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (128356097/5000000000000:ℝ) ≤ ((328629105731/200000000000:ℝ)/(324304354522899/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_796 (x : ℝ) (h₁ : (2069/512:ℝ) ≤ x) (h₂ : x ≤ (8347/2048:ℝ)) : (273038177/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1288543861/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1188835111/5000000000:ℝ) := by nlinarith
  have hc1 : (1214832919/1250000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (1214832919/1250000000:ℝ) ≤ taylorCos (1188835111/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (495854877971/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1288543861/10000000000:ℝ) + taylorErr ≤ (495854877971/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (2569962169/20000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (2569962169/20000000000:ℝ) ≤ taylorSin (1288543861/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (235533061743/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1188835111/5000000000:ℝ) + taylorErr ≤ (235533061743/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (1214832919/1250000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (495854877971/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (2569962169/20000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (235533061743/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12695225000541/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6402068818241/500000000000:ℝ) := by nlinarith
  have hp1 : (21010579366449/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (529770747717/25000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2699819706027/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (4991141049267/1000000000000:ℝ) := by nlinarith
  have hN : (341621990017/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (6537837624559/20000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (341621990017/200000000000:ℝ) (6537837624559/20000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (273038177/10000000000000:ℝ) ≤ ((341621990017/200000000000:ℝ)/(6537837624559/20000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_797 (x : ℝ) (h₁ : (2069/512:ℝ) ≤ x) (h₂ : x ≤ (4189/1024:ℝ)) : (134503623/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1288543861/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1426602133/5000000000:ℝ) := by nlinarith
  have hc1 : (191914302161/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (191914302161/200000000000:ℝ) ≤ taylorCos (1426602133/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (495854877971/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1288543861/10000000000:ℝ) + taylorErr ≤ (495854877971/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (2569962169/20000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (2569962169/20000000000:ℝ) ≤ taylorSin (1288543861/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (281464940239/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1426602133/5000000000:ℝ) + taylorErr ≤ (281464940239/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (191914302161/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (495854877971/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (2569962169/20000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (281464940239/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12695225000541/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6425845520453/500000000000:ℝ) := by nlinarith
  have hp1 : (21010579366449/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21269530726599/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2699819706027/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (2993313597437/500000000000:ℝ) := by nlinarith
  have hN : (341621990017/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20583245326363/62500000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (341621990017/200000000000:ℝ) (20583245326363/62500000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (134503623/5000000000000:ℝ) ≤ ((341621990017/200000000000:ℝ)/(20583245326363/62500000000:ℝ))^2 := by norm_num
  linarith

theorem wc_798 (x : ℝ) (h₁ : (2069/512:ℝ) ≤ x) (h₂ : x ≤ (4209/1024:ℝ)) : (263915387/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1288543861/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (3466796581/10000000000:ℝ) := by nlinarith
  have hc1 : (470253034159/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (470253034159/500000000000:ℝ) ≤ taylorCos (3466796581/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (495854877971/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1288543861/10000000000:ℝ) + taylorErr ≤ (495854877971/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (2569962169/20000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (2569962169/20000000000:ℝ) ≤ taylorSin (1288543861/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (67955377341/200000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3466796581/10000000000:ℝ) + taylorErr ≤ (67955377341/200000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (470253034159/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (495854877971/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (2569962169/20000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (67955377341/200000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12695225000541/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6456525136211/500000000000:ℝ) := by nlinarith
  have hp1 : (21010579366449/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (5342770042269/250000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2699819706027/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1815349771343/250000000000:ℝ) := by nlinarith
  have hN : (341621990017/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (83123433669049/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (341621990017/200000000000:ℝ) (83123433669049/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (263915387/10000000000000:ℝ) ≤ ((341621990017/200000000000:ℝ)/(83123433669049/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_799 (x : ℝ) (h₁ : (2069/512:ℝ) ≤ x) (h₂ : x ≤ (265/64:ℝ)) : (64064721/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1288543861/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (441786467/1000000000:ℝ) := by nlinarith
  have hc1 : (903989290823/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (903989290823/1000000000000:ℝ) ≤ taylorCos (441786467/1000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (495854877971/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1288543861/10000000000:ℝ) + taylorErr ≤ (495854877971/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (2569962169/20000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (2569962169/20000000000:ℝ) ≤ taylorSin (1288543861/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (495854877971/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (2569962169/20000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (427555095773/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12695225000541/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (13008157081271/1000000000000:ℝ) := by nlinarith
  have hp1 : (21010579366449/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21528481804913/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2699819706027/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (9204612099947/1000000000000:ℝ) := by nlinarith
  have hN : (341621990017/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (168712150651021/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (341621990017/200000000000:ℝ) (168712150651021/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (64064721/2500000000000:ℝ) ≤ ((341621990017/200000000000:ℝ)/(168712150651021/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_800 (x : ℝ) (h₁ : (2069/512:ℝ) ≤ x) (h₂ : x ≤ (535/128:ℝ)) : (246785359/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1288543861/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (56450493/100000000:ℝ) := by nlinarith
  have hc1 : (422426781477/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (422426781477/500000000000:ℝ) ≤ taylorCos (56450493/100000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (495854877971/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1288543861/10000000000:ℝ) + taylorErr ≤ (495854877971/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (2569962169/20000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (2569962169/20000000000:ℝ) ≤ taylorSin (1288543861/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (267498811099/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (56450493/100000000:ℝ) + taylorErr ≤ (267498811099/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (422426781477/500000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (495854877971/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (2569962169/20000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (267498811099/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12695225000541/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6565437772151/500000000000:ℝ) := by nlinarith
  have hp1 : (21010579366449/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10865790344933/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2699819706027/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (11626343995683/1000000000000:ℝ) := by nlinarith
  have hN : (341621990017/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (343839785119897/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (341621990017/200000000000:ℝ) (343839785119897/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (246785359/10000000000000:ℝ) ≤ ((341621990017/200000000000:ℝ)/(343839785119897/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_801 (x : ℝ) (h₁ : (2071/512:ℝ) ≤ x) (h₂ : x ≤ (8309/2048:ℝ)) : (184591317/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (352815581/2500000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (897378761/5000000000:ℝ) := by nlinarith
  have hc1 : (61496088199/62500000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (61496088199/62500000000:ℝ) ≤ taylorCos (897378761/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (123757276567/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (352815581/2500000000:ℝ) + taylorErr ≤ (123757276567/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (70329118493/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (70329118493/500000000000:ℝ) ≤ taylorSin (352815581/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (89256886609/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (897378761/5000000000:ℝ) + taylorErr ≤ (89256886609/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (61496088199/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (123757276567/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (70329118493/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (89256886609/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3176874211711/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6372923183271/500000000000:ℝ) := by nlinarith
  have hp1 : (21030889254671/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2636794742291/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2958167804809/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (3765633429183/1000000000000:ℝ) := by nlinarith
  have hN : (1968109592273/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (40489149899873/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1968109592273/1000000000000:ℝ) (40489149899873/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (184591317/5000000000000:ℝ) ≤ ((1968109592273/1000000000000:ℝ)/(40489149899873/125000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_802 (x : ℝ) (h₁ : (2071/512:ℝ) ≤ x) (h₂ : x ≤ (4157/1024:ℝ)) : (184146301/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (352815581/2500000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (935728281/5000000000:ℝ) := by nlinarith
  have hc1 : (982539300011/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (982539300011/1000000000000:ℝ) ≤ taylorCos (935728281/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (123757276567/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (352815581/2500000000:ℝ) + taylorErr ≤ (123757276567/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (70329118493/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (70329118493/500000000000:ℝ) ≤ taylorSin (352815581/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (93027577001/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (935728281/5000000000:ℝ) + taylorErr ≤ (93027577001/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (982539300011/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (123757276567/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (70329118493/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (93027577001/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3176874211711/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6376758135241/500000000000:ℝ) := by nlinarith
  have hp1 : (21030889254671/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10553525809319/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2958167804809/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1963537869717/500000000000:ℝ) := by nlinarith
  have hN : (1968109592273/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (324304354522899/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1968109592273/1000000000000:ℝ) (324304354522899/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (184146301/5000000000000:ℝ) ≤ ((1968109592273/1000000000000:ℝ)/(324304354522899/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_803 (x : ℝ) (h₁ : (2071/512:ℝ) ≤ x) (h₂ : x ≤ (2081/512:ℝ)) : (183260287/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (352815581/2500000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2024854641/10000000000:ℝ) := by nlinarith
  have hc1 : (979569763403/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (979569763403/1000000000000:ℝ) ≤ taylorCos (2024854641/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (123757276567/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (352815581/2500000000:ℝ) + taylorErr ≤ (123757276567/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (70329118493/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (70329118493/500000000000:ℝ) ≤ taylorSin (352815581/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (201104637201/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2024854641/10000000000:ℝ) + taylorErr ≤ (201104637201/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (979569763403/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (123757276567/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (70329118493/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (201104637201/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3176874211711/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12768856078361/1000000000000:ℝ) := by nlinarith
  have hp1 : (21030889254671/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21132438979257/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2958167804809/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (265614467131/62500000000:ℝ) := by nlinarith
  have hN : (1968109592273/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (162543685549897/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1968109592273/1000000000000:ℝ) (162543685549897/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (183260287/5000000000000:ℝ) ≤ ((1968109592273/1000000000000:ℝ)/(162543685549897/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_804 (x : ℝ) (h₁ : (2071/512:ℝ) ≤ x) (h₂ : x ≤ (4167/1024:ℝ)) : (182379599/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (352815581/2500000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2178252719/10000000000:ℝ) := by nlinarith
  have hc1 : (976369729063/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (976369729063/1000000000000:ℝ) ≤ taylorCos (2178252719/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (123757276567/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (352815581/2500000000:ℝ) + taylorErr ≤ (123757276567/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (70329118493/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (70329118493/500000000000:ℝ) ≤ taylorSin (352815581/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (123757276567/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (70329118493/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (108053399679/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3176874211711/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12784195886239/1000000000000:ℝ) := by nlinarith
  have hp1 : (21030889254671/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (169262610719/8000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2958167804809/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (4572350131683/1000000000000:ℝ) := by nlinarith
  have hN : (1968109592273/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (325871328915461/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1968109592273/1000000000000:ℝ) (325871328915461/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (182379599/5000000000000:ℝ) ≤ ((1968109592273/1000000000000:ℝ)/(325871328915461/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_805 (x : ℝ) (h₁ : (2071/512:ℝ) ≤ x) (h₂ : x ≤ (1043/256:ℝ)) : (90752099/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (352815581/2500000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1165825399/5000000000:ℝ) := by nlinarith
  have hc1 : (486469974967/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (486469974967/500000000000:ℝ) ≤ taylorCos (1165825399/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (123757276567/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (352815581/2500000000:ℝ) + taylorErr ≤ (123757276567/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (70329118493/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (70329118493/500000000000:ℝ) ≤ taylorSin (352815581/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (123757276567/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (70329118493/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (231058110583/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3176874211711/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6399767847059/500000000000:ℝ) := by nlinarith
  have hp1 : (21030889254671/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10591606850247/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2958167804809/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (4894553333713/1000000000000:ℝ) := by nlinarith
  have hN : (1968109592273/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (163328113985001/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1968109592273/1000000000000:ℝ) (163328113985001/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (90752099/2500000000000:ℝ) ≤ ((1968109592273/1000000000000:ℝ)/(163328113985001/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_806 (x : ℝ) (h₁ : (2071/512:ℝ) ≤ x) (h₂ : x ≤ (2091/512:ℝ)) : (89884553/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (352815581/2500000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (659611739/2500000000:ℝ) := by nlinarith
  have hc1 : (482697219707/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (482697219707/500000000000:ℝ) ≤ taylorCos (659611739/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (123757276567/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (352815581/2500000000:ℝ) + taylorErr ≤ (123757276567/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (70329118493/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (70329118493/500000000000:ℝ) ≤ taylorSin (352815581/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (123757276567/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (70329118493/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (130397060129/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3176874211711/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3207553827469/250000000000:ℝ) := by nlinarith
  have hp1 : (21030889254671/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21233988421733/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2958167804809/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1107539866003/200000000000:ℝ) := by nlinarith
  have hN : (1968109592273/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (164114424897777/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1968109592273/1000000000000:ℝ) (164114424897777/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (89884553/2500000000000:ℝ) ≤ ((1968109592273/1000000000000:ℝ)/(164114424897777/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_807 (x : ℝ) (h₁ : (2071/512:ℝ) ≤ x) (h₂ : x ≤ (131/32:ℝ)) : (17805471/500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (352815581/2500000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2945243113/10000000000:ℝ) := by nlinarith
  have hc1 : (956940333463/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (956940333463/1000000000000:ℝ) ≤ taylorCos (2945243113/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (123757276567/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (352815581/2500000000:ℝ) + taylorErr ≤ (123757276567/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (70329118493/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (70329118493/500000000000:ℝ) ≤ taylorSin (352815581/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (123757276567/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (70329118493/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (290284679541/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3176874211711/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6430447462817/500000000000:ℝ) := by nlinarith
  have hp1 : (21030889254671/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21284763142971/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (2958167804809/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (48270630063/7812500000:ℝ) := by nlinarith
  have hN : (1968109592273/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (329805236576397/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1968109592273/1000000000000:ℝ) (329805236576397/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (17805471/500000000000:ℝ) ≤ ((1968109592273/1000000000000:ℝ)/(329805236576397/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_808 (x : ℝ) (h₁ : (8287/2048:ℝ) ≤ x) (h₂ : x ≤ (4169/1024:ℝ)) : (200521187/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (364320437/2500000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2239611951/10000000000:ℝ) := by nlinarith
  have hc1 : (97502534279/100000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (97502534279/100000000000:ℝ) ≤ taylorCos (2239611951/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (989400430061/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (364320437/2500000000:ℝ) + taylorErr ≤ (989400430061/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (72606461171/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (72606461171/500000000000:ℝ) ≤ taylorSin (364320437/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (111046811651/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2239611951/10000000000:ℝ) + taylorErr ≤ (111046811651/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (97502534279/100000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (989400430061/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (72606461171/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (111046811651/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (1589012348651/125000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12790331809391/1000000000000:ℝ) := by nlinarith
  have hp1 : (4207701092551/200000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21167981284123/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (1527531429977/500000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (235063683069/50000000000:ℝ) := by nlinarith
  have hN : (2065662429893/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (326185175588639/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2065662429893/1000000000000:ℝ) (326185175588639/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (200521187/5000000000000:ℝ) ≤ ((2065662429893/1000000000000:ℝ)/(326185175588639/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_809 (x : ℝ) (h₁ : (8289/2048:ℝ) ≤ x) (h₂ : x ≤ (8309/2048:ℝ)) : (432705303/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (371990341/2500000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (897378761/5000000000:ℝ) := by nlinarith
  have hc1 : (61496088199/62500000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (61496088199/62500000000:ℝ) ≤ taylorCos (897378761/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (123618783347/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (371990341/2500000000:ℝ) + taylorErr ≤ (123618783347/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (1482476767/10000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (1482476767/10000000000:ℝ) ≤ taylorSin (371990341/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (89256886609/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (897378761/5000000000:ℝ) + taylorErr ≤ (89256886609/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (61496088199/62500000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (123618783347/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (1482476767/10000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (89256886609/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (198674480481/15625000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6372923183271/500000000000:ℝ) := by nlinarith
  have hp1 : (21043582934811/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2636794742291/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (3119662279529/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (3765633429183/1000000000000:ℝ) := by nlinarith
  have hN : (2130712012753/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (40489149899873/125000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2130712012753/1000000000000:ℝ) (40489149899873/125000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (432705303/10000000000000:ℝ) ≤ ((2130712012753/1000000000000:ℝ)/(40489149899873/125000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_810 (x : ℝ) (h₁ : (8289/2048:ℝ) ≤ x) (h₂ : x ≤ (4157/1024:ℝ)) : (431662129/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (371990341/2500000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (935728281/5000000000:ℝ) := by nlinarith
  have hc1 : (982539300011/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (982539300011/1000000000000:ℝ) ≤ taylorCos (935728281/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (123618783347/125000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (371990341/2500000000:ℝ) + taylorErr ≤ (123618783347/125000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (1482476767/10000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (1482476767/10000000000:ℝ) ≤ taylorSin (371990341/2500000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (93027577001/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (935728281/5000000000:ℝ) + taylorErr ≤ (93027577001/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (982539300011/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (123618783347/125000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (1482476767/10000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (93027577001/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (198674480481/15625000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6376758135241/500000000000:ℝ) := by nlinarith
  have hp1 : (21043582934811/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10553525809319/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (3119662279529/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1963537869717/500000000000:ℝ) := by nlinarith
  have hN : (2130712012753/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (324304354522899/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2130712012753/1000000000000:ℝ) (324304354522899/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (431662129/10000000000000:ℝ) ≤ ((2130712012753/1000000000000:ℝ)/(324304354522899/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_811 (x : ℝ) (h₁ : (4147/1024:ℝ) ≤ x) (h₂ : x ≤ (4157/1024:ℝ)) : (20003551/400000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1564660403/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (935728281/5000000000:ℝ) := by nlinarith
  have hc1 : (982539300011/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (982539300011/1000000000000:ℝ) ≤ taylorCos (935728281/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (987784143917/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1564660403/10000000000:ℝ) + taylorErr ≤ (987784143917/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (155828395329/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (155828395329/1000000000000:ℝ) ≤ taylorSin (1564660403/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (93027577001/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (935728281/5000000000:ℝ) + taylorErr ≤ (93027577001/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (982539300011/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (987784143917/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (155828395329/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (93027577001/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12722836654723/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6376758135241/500000000000:ℝ) := by nlinarith
  have hp1 : (421125532299/20000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10553525809319/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (3281165796511/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1963537869717/500000000000:ℝ) := by nlinarith
  have hN : (1146690826297/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (324304354522899/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1146690826297/500000000000:ℝ) (324304354522899/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (20003551/400000000000:ℝ) ≤ ((1146690826297/500000000000:ℝ)/(324304354522899/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_812 (x : ℝ) (h₁ : (4147/1024:ℝ) ≤ x) (h₂ : x ≤ (8319/2048:ℝ)) : (498883881/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1564660403/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1948155601/10000000000:ℝ) := by nlinarith
  have hc1 : (981083388881/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (981083388881/1000000000000:ℝ) ≤ taylorCos (1948155601/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (987784143917/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1564660403/10000000000:ℝ) + taylorErr ≤ (987784143917/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (155828395329/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (155828395329/1000000000000:ℝ) ≤ taylorSin (1564660403/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (48396397399/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1948155601/10000000000:ℝ) + taylorErr ≤ (48396397399/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (981083388881/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (987784143917/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (155828395329/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (48396397399/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12722836654723/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12761186174421/1000000000000:ℝ) := by nlinarith
  have hp1 : (421125532299/20000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21119745298947/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (3281165796511/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (817695669163/200000000000:ℝ) := by nlinarith
  have hN : (1146690826297/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (81173936289117/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1146690826297/500000000000:ℝ) (81173936289117/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (498883881/10000000000000:ℝ) ≤ ((1146690826297/500000000000:ℝ)/(81173936289117/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_813 (x : ℝ) (h₁ : (4147/1024:ℝ) ≤ x) (h₂ : x ≤ (2081/512:ℝ)) : (99536523/2000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1564660403/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2024854641/10000000000:ℝ) := by nlinarith
  have hc1 : (979569763403/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (979569763403/1000000000000:ℝ) ≤ taylorCos (2024854641/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (987784143917/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1564660403/10000000000:ℝ) + taylorErr ≤ (987784143917/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (155828395329/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (155828395329/1000000000000:ℝ) ≤ taylorSin (1564660403/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (201104637201/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2024854641/10000000000:ℝ) + taylorErr ≤ (201104637201/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (979569763403/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (987784143917/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (155828395329/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (201104637201/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12722836654723/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12768856078361/1000000000000:ℝ) := by nlinarith
  have hp1 : (421125532299/20000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21132438979257/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (3281165796511/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (265614467131/62500000000:ℝ) := by nlinarith
  have hN : (1146690826297/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (162543685549897/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1146690826297/500000000000:ℝ) (162543685549897/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (99536523/2000000000000:ℝ) ≤ ((1146690826297/500000000000:ℝ)/(162543685549897/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_814 (x : ℝ) (h₁ : (4147/1024:ℝ) ≤ x) (h₂ : x ≤ (4167/1024:ℝ)) : (495290917/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1564660403/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2178252719/10000000000:ℝ) := by nlinarith
  have hc1 : (976369729063/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (976369729063/1000000000000:ℝ) ≤ taylorCos (2178252719/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (987784143917/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1564660403/10000000000:ℝ) + taylorErr ≤ (987784143917/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (155828395329/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (155828395329/1000000000000:ℝ) ≤ taylorSin (1564660403/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (987784143917/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (155828395329/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (108053399679/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12722836654723/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12784195886239/1000000000000:ℝ) := by nlinarith
  have hp1 : (421125532299/20000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (169262610719/8000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (3281165796511/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (4572350131683/1000000000000:ℝ) := by nlinarith
  have hN : (1146690826297/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (325871328915461/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1146690826297/500000000000:ℝ) (325871328915461/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (495290917/10000000000000:ℝ) ≤ ((1146690826297/500000000000:ℝ)/(325871328915461/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_815 (x : ℝ) (h₁ : (4149/1024:ℝ) ≤ x) (h₂ : x ≤ (525/128:ℝ)) : (267941559/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (325203927/2000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (3190680039/10000000000:ℝ) := by nlinarith
  have hc1 : (37981127133/40000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (37981127133/40000000000:ℝ) ≤ taylorCos (3190680039/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (986809404079/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (325203927/2000000000:ℝ) + taylorErr ≤ (986809404079/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (80943195751/500000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (80943195751/500000000000:ℝ) ≤ taylorSin (325203927/2000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (7842043567/25000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3190680039/10000000000:ℝ) + taylorErr ≤ (7842043567/25000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (37981127133/40000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (986809404079/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (80943195751/500000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (7842043567/25000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (101831780623/8000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (20133497841/1562500000:ℝ) := by nlinarith
  have hp1 : (10533215779531/500000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21325382919961/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (85259214673/25000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1672345819413/250000000000:ℝ) := by nlinarith
  have hN : (2423559182841/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (165534528384431/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2423559182841/1000000000000:ℝ) (165534528384431/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (267941559/5000000000000:ℝ) ≤ ((2423559182841/1000000000000:ℝ)/(165534528384431/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_816 (x : ℝ) (h₁ : (8299/2048:ℝ) ≤ x) (h₂ : x ≤ (4157/1024:ℝ)) : (573574207/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1641359443/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (935728281/5000000000:ℝ) := by nlinarith
  have hc1 : (982539300011/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (982539300011/1000000000000:ℝ) ≤ taylorCos (935728281/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (61659994533/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1641359443/10000000000:ℝ) + taylorErr ≤ (61659994533/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (163399947117/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (163399947117/1000000000000:ℝ) ≤ taylorSin (1641359443/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (93027577001/500000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (935728281/5000000000:ℝ) + taylorErr ≤ (93027577001/500000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (982539300011/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (61659994533/62500000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (163399947117/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (93027577001/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6365253279331/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6376758135241/500000000000:ℝ) := by nlinarith
  have hp1 : (21068970295089/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10553525809319/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (3442668632027/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1963537869717/500000000000:ℝ) := by nlinarith
  have hN : (2456108719499/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (324304354522899/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2456108719499/1000000000000:ℝ) (324304354522899/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (573574207/10000000000000:ℝ) ≤ ((2456108719499/1000000000000:ℝ)/(324304354522899/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_817 (x : ℝ) (h₁ : (8299/2048:ℝ) ≤ x) (h₂ : x ≤ (8319/2048:ℝ)) : (572192259/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1641359443/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1948155601/10000000000:ℝ) := by nlinarith
  have hc1 : (981083388881/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (981083388881/1000000000000:ℝ) ≤ taylorCos (1948155601/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (61659994533/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1641359443/10000000000:ℝ) + taylorErr ≤ (61659994533/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (163399947117/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (163399947117/1000000000000:ℝ) ≤ taylorSin (1641359443/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (48396397399/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1948155601/10000000000:ℝ) + taylorErr ≤ (48396397399/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (981083388881/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (61659994533/62500000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (163399947117/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (48396397399/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6365253279331/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12761186174421/1000000000000:ℝ) := by nlinarith
  have hp1 : (21068970295089/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21119745298947/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (3442668632027/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (817695669163/200000000000:ℝ) := by nlinarith
  have hN : (2456108719499/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (81173936289117/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2456108719499/1000000000000:ℝ) (81173936289117/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (572192259/10000000000000:ℝ) ≤ ((2456108719499/1000000000000:ℝ)/(81173936289117/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_818 (x : ℝ) (h₁ : (8299/2048:ℝ) ≤ x) (h₂ : x ≤ (2081/512:ℝ)) : (570814473/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1641359443/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2024854641/10000000000:ℝ) := by nlinarith
  have hc1 : (979569763403/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (979569763403/1000000000000:ℝ) ≤ taylorCos (2024854641/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (61659994533/62500000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1641359443/10000000000:ℝ) + taylorErr ≤ (61659994533/62500000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (163399947117/1000000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (163399947117/1000000000000:ℝ) ≤ taylorSin (1641359443/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (201104637201/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2024854641/10000000000:ℝ) + taylorErr ≤ (201104637201/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (979569763403/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (61659994533/62500000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (163399947117/1000000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (201104637201/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6365253279331/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12768856078361/1000000000000:ℝ) := by nlinarith
  have hp1 : (21068970295089/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21132438979257/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (3442668632027/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (265614467131/62500000000:ℝ) := by nlinarith
  have hN : (2456108719499/1000000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (162543685549897/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (2456108719499/1000000000000:ℝ) (162543685549897/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (570814473/10000000000000:ℝ) ≤ ((2456108719499/1000000000000:ℝ)/(162543685549897/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_819 (x : ℝ) (h₁ : (519/128:ℝ) ≤ x) (h₂ : x ≤ (16633/4096:ℝ)) : (325666339/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (859029241/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1909806081/10000000000:ℝ) := by nlinarith
  have hc1 : (981818564179/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (981818564179/1000000000000:ℝ) ≤ taylorCos (1909806081/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (492638822329/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (859029241/5000000000:ℝ) + taylorErr ≤ (492638822329/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (21370235807/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (21370235807/125000000000:ℝ) ≤ taylorSin (859029241/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (189821767589/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1909806081/10000000000:ℝ) + taylorErr ≤ (189821767589/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (981818564179/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (492638822329/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (21370235807/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (189821767589/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6369088231301/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12757351222451/1000000000000:ℝ) := by nlinarith
  have hp1 : (21081663975229/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (2639174807349/125000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (901040260709/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (4007782615259/1000000000000:ℝ) := by nlinarith
  have hN : (1309441699089/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (64900004085189/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1309441699089/500000000000:ℝ) (64900004085189/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (325666339/5000000000000:ℝ) ≤ ((1309441699089/500000000000:ℝ)/(64900004085189/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_820 (x : ℝ) (h₁ : (519/128:ℝ) ≤ x) (h₂ : x ≤ (8319/2048:ℝ)) : (162636919/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (859029241/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1948155601/10000000000:ℝ) := by nlinarith
  have hc1 : (981083388881/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (981083388881/1000000000000:ℝ) ≤ taylorCos (1948155601/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (492638822329/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (859029241/5000000000:ℝ) + taylorErr ≤ (492638822329/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (21370235807/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (21370235807/125000000000:ℝ) ≤ taylorSin (859029241/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (48396397399/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1948155601/10000000000:ℝ) + taylorErr ≤ (48396397399/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (981083388881/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (492638822329/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (21370235807/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (48396397399/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6369088231301/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12761186174421/1000000000000:ℝ) := by nlinarith
  have hp1 : (21081663975229/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21119745298947/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (901040260709/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (817695669163/200000000000:ℝ) := by nlinarith
  have hN : (1309441699089/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (81173936289117/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1309441699089/500000000000:ℝ) (81173936289117/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (162636919/2500000000000:ℝ) ≤ ((1309441699089/500000000000:ℝ)/(81173936289117/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_821 (x : ℝ) (h₁ : (519/128:ℝ) ≤ x) (h₂ : x ≤ (2081/512:ℝ)) : (648981217/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (859029241/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2024854641/10000000000:ℝ) := by nlinarith
  have hc1 : (979569763403/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (979569763403/1000000000000:ℝ) ≤ taylorCos (2024854641/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (492638822329/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (859029241/5000000000:ℝ) + taylorErr ≤ (492638822329/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (21370235807/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (21370235807/125000000000:ℝ) ≤ taylorSin (859029241/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (201104637201/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2024854641/10000000000:ℝ) + taylorErr ≤ (201104637201/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (979569763403/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (492638822329/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (21370235807/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (201104637201/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6369088231301/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12768856078361/1000000000000:ℝ) := by nlinarith
  have hp1 : (21081663975229/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21132438979257/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (901040260709/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (265614467131/62500000000:ℝ) := by nlinarith
  have hN : (1309441699089/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (162543685549897/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1309441699089/500000000000:ℝ) (162543685549897/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (648981217/10000000000000:ℝ) ≤ ((1309441699089/500000000000:ℝ)/(162543685549897/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_822 (x : ℝ) (h₁ : (519/128:ℝ) ≤ x) (h₂ : x ≤ (8329/2048:ℝ)) : (323709737/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (859029241/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (26269421/125000000:ℝ) := by nlinarith
  have hc1 : (48899925633/50000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (48899925633/50000000000:ℝ) ≤ taylorCos (26269421/125000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (492638822329/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (859029241/5000000000:ℝ) + taylorErr ≤ (492638822329/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (21370235807/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (21370235807/125000000000:ℝ) ≤ taylorSin (859029241/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (208611854299/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (26269421/125000000:ℝ) + taylorErr ≤ (208611854299/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (48899925633/50000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (492638822329/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (21370235807/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (208611854299/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6369088231301/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (127765259823/10000000000:ℝ) := by nlinarith
  have hp1 : (21081663975229/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10572566329783/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (901040260709/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (4411125333511/1000000000000:ℝ) := by nlinarith
  have hN : (1309441699089/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (162739616176387/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1309441699089/500000000000:ℝ) (162739616176387/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (323709737/5000000000000:ℝ) ≤ ((1309441699089/500000000000:ℝ)/(162739616176387/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_823 (x : ℝ) (h₁ : (519/128:ℝ) ≤ x) (h₂ : x ≤ (4167/1024:ℝ)) : (645862429/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (859029241/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2178252719/10000000000:ℝ) := by nlinarith
  have hc1 : (976369729063/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (976369729063/1000000000000:ℝ) ≤ taylorCos (2178252719/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (492638822329/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (859029241/5000000000:ℝ) + taylorErr ≤ (492638822329/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (21370235807/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (21370235807/125000000000:ℝ) ≤ taylorSin (859029241/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (492638822329/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (21370235807/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (108053399679/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6369088231301/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12784195886239/1000000000000:ℝ) := by nlinarith
  have hp1 : (21081663975229/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (169262610719/8000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (901040260709/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (4572350131683/1000000000000:ℝ) := by nlinarith
  have hN : (1309441699089/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (325871328915461/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1309441699089/500000000000:ℝ) (325871328915461/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (645862429/10000000000000:ℝ) ≤ ((1309441699089/500000000000:ℝ)/(325871328915461/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_824 (x : ℝ) (h₁ : (519/128:ℝ) ≤ x) (h₂ : x ≤ (1043/256:ℝ)) : (160690591/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (859029241/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1165825399/5000000000:ℝ) := by nlinarith
  have hc1 : (486469974967/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (486469974967/500000000000:ℝ) ≤ taylorCos (1165825399/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (492638822329/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (859029241/5000000000:ℝ) + taylorErr ≤ (492638822329/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (21370235807/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (21370235807/125000000000:ℝ) ≤ taylorSin (859029241/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (492638822329/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (21370235807/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (231058110583/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6369088231301/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6399767847059/500000000000:ℝ) := by nlinarith
  have hp1 : (21081663975229/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10591606850247/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (901040260709/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (4894553333713/1000000000000:ℝ) := by nlinarith
  have hN : (1309441699089/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (163328113985001/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1309441699089/500000000000:ℝ) (163328113985001/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (160690591/2500000000000:ℝ) ≤ ((1309441699089/500000000000:ℝ)/(163328113985001/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_825 (x : ℝ) (h₁ : (519/128:ℝ) ≤ x) (h₂ : x ≤ (4177/1024:ℝ)) : (79960111/1250000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (859029241/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2485048877/10000000000:ℝ) := by nlinarith
  have hc1 : (969281233079/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (969281233079/1000000000000:ℝ) ≤ taylorCos (2485048877/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (492638822329/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (859029241/5000000000:ℝ) + taylorErr ≤ (492638822329/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (21370235807/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (21370235807/125000000000:ℝ) ≤ taylorSin (859029241/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (492638822329/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (21370235807/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (245955052659/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6369088231301/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12814875501997/1000000000000:ℝ) := by nlinarith
  have hp1 : (21081663975229/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21208601061113/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (901040260709/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (521636259081/100000000000:ℝ) := by nlinarith
  have hN : (1309441699089/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (163721034131683/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1309441699089/500000000000:ℝ) (163721034131683/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (79960111/1250000000000:ℝ) ≤ ((1309441699089/500000000000:ℝ)/(163721034131683/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_826 (x : ℝ) (h₁ : (519/128:ℝ) ≤ x) (h₂ : x ≤ (2091/512:ℝ)) : (636617867/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (859029241/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (659611739/2500000000:ℝ) := by nlinarith
  have hc1 : (482697219707/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (482697219707/500000000000:ℝ) ≤ taylorCos (659611739/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (492638822329/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (859029241/5000000000:ℝ) + taylorErr ≤ (492638822329/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (21370235807/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (21370235807/125000000000:ℝ) ≤ taylorSin (859029241/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (492638822329/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (21370235807/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (130397060129/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6369088231301/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (3207553827469/250000000000:ℝ) := by nlinarith
  have hp1 : (21081663975229/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21233988421733/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (901040260709/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1107539866003/200000000000:ℝ) := by nlinarith
  have hN : (1309441699089/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (164114424897777/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1309441699089/500000000000:ℝ) (164114424897777/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (636617867/10000000000000:ℝ) ≤ ((1309441699089/500000000000:ℝ)/(164114424897777/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_827 (x : ℝ) (h₁ : (519/128:ℝ) ≤ x) (h₂ : x ≤ (131/32:ℝ)) : (315273331/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (859029241/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2945243113/10000000000:ℝ) := by nlinarith
  have hc1 : (956940333463/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (956940333463/1000000000000:ℝ) ≤ taylorCos (2945243113/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (492638822329/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (859029241/5000000000:ℝ) + taylorErr ≤ (492638822329/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (21370235807/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (21370235807/125000000000:ℝ) ≤ taylorSin (859029241/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (492638822329/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (21370235807/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (290284679541/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6369088231301/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6430447462817/500000000000:ℝ) := by nlinarith
  have hp1 : (21081663975229/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21284763142971/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (901040260709/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (48270630063/7812500000:ℝ) := by nlinarith
  have hN : (1309441699089/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (329805236576397/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1309441699089/500000000000:ℝ) (329805236576397/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (315273331/5000000000000:ℝ) ≤ ((1309441699089/500000000000:ℝ)/(329805236576397/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_828 (x : ℝ) (h₁ : (519/128:ℝ) ≤ x) (h₂ : x ≤ (2101/512:ℝ)) : (624547701/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (859029241/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (3252039271/10000000000:ℝ) := by nlinarith
  have hc1 : (473792794367/500000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (473792794367/500000000000:ℝ) ≤ taylorCos (3252039271/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (492638822329/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (859029241/5000000000:ℝ) + taylorErr ≤ (492638822329/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (21370235807/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (21370235807/125000000000:ℝ) ≤ taylorSin (859029241/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (492638822329/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (21370235807/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (319502033143/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6369088231301/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12891574541391/1000000000000:ℝ) := by nlinarith
  have hp1 : (21081663975229/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (1333471116513/62500000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (901040260709/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (3408373862907/500000000000:ℝ) := by nlinarith
  have hN : (1309441699089/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (165692694156241/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1309441699089/500000000000:ℝ) (165692694156241/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (624547701/10000000000000:ℝ) ≤ ((1309441699089/500000000000:ℝ)/(165692694156241/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_829 (x : ℝ) (h₁ : (519/128:ℝ) ≤ x) (h₂ : x ≤ (1053/256:ℝ)) : (154654989/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (859029241/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (889708857/2500000000:ℝ) := by nlinarith
  have hc1 : (937339009647/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (937339009647/1000000000000:ℝ) ≤ taylorCos (889708857/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (492638822329/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (859029241/5000000000:ℝ) + taylorErr ≤ (492638822329/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (21370235807/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (21370235807/125000000000:ℝ) ≤ taylorSin (859029241/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (492638822329/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (21370235807/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (348418682521/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6369088231301/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12922254157149/1000000000000:ℝ) := by nlinarith
  have hp1 : (21081663975229/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10693156292723/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (901040260709/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1862847713751/250000000000:ℝ) := by nlinarith
  have hN : (1309441699089/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (33296930500391/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1309441699089/500000000000:ℝ) (33296930500391/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (154654989/2500000000000:ℝ) ≤ ((1309441699089/500000000000:ℝ)/(33296930500391/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_830 (x : ℝ) (h₁ : (519/128:ℝ) ≤ x) (h₂ : x ≤ (529/128:ℝ)) : (24278963/400000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (859029241/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (130388367/312500000:ℝ) := by nlinarith
  have hc1 : (914209753403/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (914209753403/1000000000000:ℝ) ≤ taylorCos (130388367/312500000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (492638822329/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (859029241/5000000000:ℝ) + taylorErr ≤ (492638822329/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (21370235807/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (21370235807/125000000000:ℝ) ≤ taylorSin (859029241/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (492638822329/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (21370235807/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (202620658177/500000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6369088231301/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2596722677733/200000000000:ℝ) := by nlinarith
  have hp1 : (21081663975229/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21487862027923/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (901040260709/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (8707769493829/1000000000000:ℝ) := by nlinarith
  have hN : (1309441699089/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (336148433252643/1000000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1309441699089/500000000000:ℝ) (336148433252643/1000000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (24278963/400000000000:ℝ) ≤ ((1309441699089/500000000000:ℝ)/(336148433252643/1000000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_831 (x : ℝ) (h₁ : (519/128:ℝ) ≤ x) (h₂ : x ≤ (1063/256:ℝ)) : (297800559/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (859029241/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (4786020059/10000000000:ℝ) := by nlinarith
  have hc1 : (110954952263/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (110954952263/125000000000:ℝ) ≤ taylorCos (4786020059/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (492638822329/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (859029241/5000000000:ℝ) + taylorErr ≤ (492638822329/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (21370235807/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (21370235807/125000000000:ℝ) ≤ taylorSin (859029241/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (492638822329/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (21370235807/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (460538713291/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6369088231301/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (652248631009/50000000000:ℝ) := by nlinarith
  have hp1 : (21081663975229/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21589411470399/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (901040260709/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (1242844972411/125000000000:ℝ) := by nlinarith
  have hN : (1309441699089/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (84835655330623/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1309441699089/500000000000:ℝ) (84835655330623/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (297800559/5000000000000:ℝ) ≤ ((1309441699089/500000000000:ℝ)/(84835655330623/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_832 (x : ℝ) (h₁ : (519/128:ℝ) ≤ x) (h₂ : x ≤ (267/64:ℝ)) : (913271/15625000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (859029241/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2699806187/5000000000:ℝ) := by nlinarith
  have hc1 : (107216075963/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (107216075963/125000000000:ℝ) ≤ taylorCos (2699806187/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (492638822329/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (859029241/5000000000:ℝ) + taylorErr ≤ (492638822329/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (21370235807/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (21370235807/125000000000:ℝ) ≤ taylorSin (859029241/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
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
  have hcxu : Real.cos (Real.pi*x) ≤ (492638822329/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (21370235807/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (51410274651/100000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6369088231301/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (2621266370339/200000000000:ℝ) := by nlinarith
  have hp1 : (21081663975229/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10845480456437/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (901040260709/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (44605530319/4000000000:ℝ) := by nlinarith
  have hN : (1309441699089/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (34255186921351/100000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1309441699089/500000000000:ℝ) (34255186921351/100000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (913271/15625000000:ℝ) ≤ ((1309441699089/500000000000:ℝ)/(34255186921351/100000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_833 (x : ℝ) (h₁ : (519/128:ℝ) ≤ x) (h₂ : x ≤ (539/128:ℝ)) : (563044583/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (859029241/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1656699251/2500000000:ℝ) := by nlinarith
  have hc1 : (788346425329/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (788346425329/1000000000000:ℝ) ≤ taylorCos (1656699251/2500000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (492638822329/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (859029241/5000000000:ℝ) + taylorErr ≤ (492638822329/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (21370235807/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (21370235807/125000000000:ℝ) ≤ taylorSin (859029241/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (153807898217/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1656699251/2500000000:ℝ) + taylorErr ≤ (153807898217/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (788346425329/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (492638822329/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (21370235807/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (153807898217/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6369088231301/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6614525157363/500000000000:ℝ) := by nlinarith
  have hp1 : (21081663975229/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10947029898913/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (901040260709/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (3367479320941/250000000000:ℝ) := by nlinarith
  have hN : (1309441699089/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (69803108891821/200000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1309441699089/500000000000:ℝ) (69803108891821/200000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (563044583/10000000000000:ℝ) ≤ ((1309441699089/500000000000:ℝ)/(69803108891821/200000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_834 (x : ℝ) (h₁ : (519/128:ℝ) ≤ x) (h₂ : x ≤ (17/4:ℝ)) : (271285583/5000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (859029241/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (3926990817/5000000000:ℝ) := by nlinarith
  have hc1 : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (88388347351/125000000000:ℝ) ≤ taylorCos (3926990817/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (492638822329/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (859029241/5000000000:ℝ) + taylorErr ≤ (492638822329/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (21370235807/125000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (21370235807/125000000000:ℝ) ≤ taylorSin (859029241/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (176776695861/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (3926990817/5000000000:ℝ) + taylorErr ≤ (176776695861/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (88388347351/125000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (492638822329/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (21370235807/125000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (176776695861/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6369088231301/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (13351768777757/1000000000000:ℝ) := by nlinarith
  have hp1 : (21081663975229/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (11048579341389/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (901040260709/250000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (15625050799431/1000000000000:ℝ) := by nlinarith
  have hN : (1309441699089/500000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (177769729494687/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (1309441699089/500000000000:ℝ) (177769729494687/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (271285583/5000000000000:ℝ) ≤ ((1309441699089/500000000000:ℝ)/(177769729494687/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_835 (x : ℝ) (h₁ : (16613/4096:ℝ) ≤ x) (h₂ : x ≤ (8319/2048:ℝ)) : (69161783/1000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (878204001/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1948155601/10000000000:ℝ) := by nlinarith
  have hc1 : (981083388881/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (981083388881/1000000000000:ℝ) ≤ taylorCos (1948155601/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (984614770469/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (878204001/5000000000:ℝ) + taylorErr ≤ (984614770469/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (34947822501/200000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (34947822501/200000000000:ℝ) ≤ taylorSin (878204001/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (48396397399/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1948155601/10000000000:ℝ) + taylorErr ≤ (48396397399/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (981083388881/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (984614770469/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (34947822501/200000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (48396397399/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (3185502853643/250000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12761186174421/1000000000000:ℝ) := by nlinarith
  have hp1 : (21088010815299/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21119745298947/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (3684900294361/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (817695669163/200000000000:ℝ) := by nlinarith
  have hN : (675071380973/250000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (81173936289117/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (675071380973/250000000000:ℝ) (81173936289117/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (69161783/1000000000000:ℝ) ≤ ((675071380973/250000000000:ℝ)/(81173936289117/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_836 (x : ℝ) (h₁ : (8307/2048:ℝ) ≤ x) (h₂ : x ≤ (4189/1024:ℝ)) : (170103471/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (882038953/5000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1426602133/5000000000:ℝ) := by nlinarith
  have hc1 : (191914302161/200000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (191914302161/200000000000:ℝ) ≤ taylorCos (1426602133/5000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (984480457647/1000000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (882038953/5000000000:ℝ) + taylorErr ≤ (984480457647/1000000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (43873562777/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (43873562777/250000000000:ℝ) ≤ taylorSin (882038953/5000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (281464940239/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1426602133/5000000000:ℝ) + taylorErr ≤ (281464940239/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (191914302161/200000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (984480457647/1000000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (43873562777/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (281464940239/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (6371389202483/500000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (6425845520453/500000000000:ℝ) := by nlinarith
  have hp1 : (21089280183313/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21269530726599/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (3701047432177/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (2993313597437/500000000000:ℝ) := by nlinarith
  have hN : (271656697453/100000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (20583245326363/62500000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (271656697453/100000000000:ℝ) (20583245326363/62500000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (170103471/2500000000000:ℝ) ≤ ((271656697453/100000000000:ℝ)/(20583245326363/62500000000:ℝ))^2 := by norm_num
  linarith

theorem wc_837 (x : ℝ) (h₁ : (8309/2048:ℝ) ≤ x) (h₂ : x ≤ (8319/2048:ℝ)) : (733949357/10000000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1794757521/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1948155601/10000000000:ℝ) := by nlinarith
  have hc1 : (981083388881/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (981083388881/1000000000000:ℝ) ≤ taylorCos (1948155601/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (491968707863/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1794757521/10000000000:ℝ) + taylorErr ≤ (491968707863/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (44628442149/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (44628442149/250000000000:ℝ) ≤ taylorSin (1794757521/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (48396397399/250000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1948155601/10000000000:ℝ) + taylorErr ≤ (48396397399/250000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (981083388881/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (491968707863/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (44628442149/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (48396397399/250000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12745846366541/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12761186174421/1000000000000:ℝ) := by nlinarith
  have hp1 : (21094357655367/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21119745298947/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (3765633281171/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (817695669163/200000000000:ℝ) := by nlinarith
  have hN : (556339173089/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (81173936289117/250000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (556339173089/200000000000:ℝ) (81173936289117/250000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (733949357/10000000000000:ℝ) ≤ ((556339173089/200000000000:ℝ)/(81173936289117/250000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_838 (x : ℝ) (h₁ : (8309/2048:ℝ) ≤ x) (h₂ : x ≤ (16643/4096:ℝ)) : (14661301/200000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1794757521/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (1986505121/10000000000:ℝ) := by nlinarith
  have hc1 : (245083446237/250000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (245083446237/250000000000:ℝ) ≤ taylorCos (1986505121/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (491968707863/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1794757521/10000000000:ℝ) + taylorErr ≤ (491968707863/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (44628442149/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (44628442149/250000000000:ℝ) ≤ taylorSin (1794757521/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (197346564571/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (1986505121/10000000000:ℝ) + taylorErr ≤ (197346564571/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (245083446237/250000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (491968707863/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (44628442149/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (197346564571/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12745846366541/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12765021126391/1000000000000:ℝ) := by nlinarith
  have hp1 : (21094357655367/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (10563046069551/500000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (3765633281171/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (4169161706463/1000000000000:ℝ) := by nlinarith
  have hN : (556339173089/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (162445764357209/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (556339173089/200000000000:ℝ) (162445764357209/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (14661301/200000000000:ℝ) ≤ ((556339173089/200000000000:ℝ)/(162445764357209/500000000000:ℝ))^2 := by norm_num
  linarith

theorem wc_839 (x : ℝ) (h₁ : (8309/2048:ℝ) ≤ x) (h₂ : x ≤ (2081/512:ℝ)) : (183045519/2500000000000:ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have hg := gam_bounds
  have ht1 : (1794757521/10000000000:ℝ) ≤ Real.pi * (x - (4:ℝ)) := by nlinarith
  have ht2 : Real.pi * (x - (4:ℝ)) ≤ (2024854641/10000000000:ℝ) := by nlinarith
  have hc1 : (979569763403/1000000000000:ℝ) ≤ Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := cos_lower (by linarith) ht2 (by norm_num)
    have h2 : (979569763403/1000000000000:ℝ) ≤ taylorCos (2024854641/10000000000:ℝ) - taylorErr := by unfold taylorCos taylorErr; norm_num
    linarith
  have hc2 : Real.cos (Real.pi * (x - (4:ℝ))) ≤ (491968707863/500000000000:ℝ) := by
    have h := cos_upper (by norm_num) ht1 (by linarith)
    have h2 : taylorCos (1794757521/10000000000:ℝ) + taylorErr ≤ (491968707863/500000000000:ℝ) := by unfold taylorCos taylorErr; norm_num
    linarith
  have hs1 : (44628442149/250000000000:ℝ) ≤ Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := sin_lower (by norm_num) ht1 (by linarith)
    have h2 : (44628442149/250000000000:ℝ) ≤ taylorSin (1794757521/10000000000:ℝ) - taylorErr := by unfold taylorSin taylorErr; norm_num
    linarith
  have hs2 : Real.sin (Real.pi * (x - (4:ℝ))) ≤ (201104637201/1000000000000:ℝ) := by
    have h := sin_upper (by linarith) ht2 (by norm_num)
    have h2 : taylorSin (2024854641/10000000000:ℝ) + taylorErr ≤ (201104637201/1000000000000:ℝ) := by unfold taylorSin taylorErr; norm_num
    linarith
  have hcx : Real.cos (Real.pi*x) = (1:ℝ) * Real.cos (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).1
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hsx : Real.sin (Real.pi*x) = (1:ℝ) * Real.sin (Real.pi * (x - (4:ℝ))) := by
    have h := (trig_shift (4:ℝ) (x - (4:ℝ))).2
    rw [show (4:ℝ) + (x - (4:ℝ)) = x by ring, cs_4.1, cs_4.2] at h
    rw [h]; ring
  have hcxl : (979569763403/1000000000000:ℝ) ≤ Real.cos (Real.pi*x) := by rw [hcx]; linarith
  have hcxu : Real.cos (Real.pi*x) ≤ (491968707863/500000000000:ℝ) := by rw [hcx]; linarith
  have hsxl : (44628442149/250000000000:ℝ) ≤ Real.sin (Real.pi*x) := by rw [hsx]; linarith
  have hsxu : Real.sin (Real.pi*x) ≤ (201104637201/1000000000000:ℝ) := by rw [hsx]; linarith
  have hb1 : (12745846366541/1000000000000:ℝ) ≤ Real.pi*x := by nlinarith
  have hb2 : Real.pi*x ≤ (12768856078361/1000000000000:ℝ) := by nlinarith
  have hp1 : (21094357655367/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x) := by nlinarith [hg.1, hg.2]
  have hp2 : 2*gam*(Real.pi*x) ≤ (21132438979257/1000000000000:ℝ) := by nlinarith [hg.1, hg.2]
  have hT1 : (3765633281171/1000000000000:ℝ) ≤ 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) := by nlinarith
  have hT2 : 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) ≤ (265614467131/62500000000:ℝ) := by nlinarith
  have hN : (556339173089/200000000000:ℝ) ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)| :=
    abs_ge_of_ge (by linarith)
  have hD0 : (1:ℝ) < 2*(Real.pi*x)^2 := by nlinarith
  have hD : 2*(Real.pi*x)^2 - 1 ≤ (162543685549897/500000000000:ℝ) := by nlinarith
  have hfin := wfun_ge x (556339173089/200000000000:ℝ) (162543685549897/500000000000:ℝ) (by norm_num) (by norm_num) hD0 hD hN
  have hsq : (183045519/2500000000000:ℝ) ≤ ((556339173089/200000000000:ℝ)/(162543685549897/500000000000:ℝ))^2 := by norm_num
  linarith

end Zeta23Ext.Bridge.FourPoint
